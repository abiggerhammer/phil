{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types (AssuranceManifest (..))
import Phil.Compiler.RuntimeChoiceTargets
  ( phase1RuntimeChoiceAArch64AppleDarwinTarget
  )
import Phil.LLVM.IR
  ( LLVMArtifact (..)
  , LLVMModule (..)
  , LLVMTargetProfile (..)
  )
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.Systems.IR (SystemsArtifact)
import Phil.Systems.Phase1Stage (phase1StageSystemsArtifact)
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , concreteSubjectStage
  )
import Phil.Systems.SubjectCorrespondence (SubjectStageBundle (..))
import Phil.Test.Phase1.CertifiedReleaseWitnesses (conventionalTrust)
import Phil.Test.Phase1.ManifestWitnesses
  ( RealManifestFixture (..)
  , steveRealManifestFixture
  )
import Phil.Verification.CertifiedRelease
import Phil.Verification.ReleasePackage
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  stevePut <- TextIO.readFile "examples/steve/put.phil"
  steveGet <- TextIO.readFile "examples/steve/get.phil"
  fixture <- requireFixture (steveRealManifestFixture stevePut steveGet)
  release <- requireRelease fixture
  package <- requirePackage fixture release
  args <- getArgs
  case args of
    [] -> runChecks release package
    ["emit-package"] -> TextIO.putStr (renderCertifiedReleasePackage package)
    ["emit-llvm"] -> TextIO.putStr
      (llvmArtifactText (certifiedReleaseLLVMArtifact release))
    _ -> do
      putStrLn "usage: Phase1TargetAArch64AppleDarwinReleasePackageMain.hs [emit-package|emit-llvm]"
      exitFailure

requireFixture :: Either String RealManifestFixture -> IO RealManifestFixture
requireFixture result = case result of
  Left detail -> do
    putStrLn ("FAIL: TARGET-AARCH64-APPLE-DARWIN release fixture -- " <> detail)
    exitFailure
  Right fixture -> pure fixture

requireRelease :: RealManifestFixture -> IO CertifiedReleaseArtifact
requireRelease fixture = case certifyDarwinFixture fixture of
  Left err -> do
    putStrLn ("FAIL: TARGET-AARCH64-APPLE-DARWIN certified release -- " <> show err)
    exitFailure
  Right release -> pure release

requirePackage
  :: RealManifestFixture
  -> CertifiedReleaseArtifact
  -> IO CertifiedReleasePackage
requirePackage fixture release =
  case buildCertifiedReleasePackage (realFixtureLedger fixture) release of
    Left err -> do
      putStrLn ("FAIL: TARGET-AARCH64-APPLE-DARWIN release package -- " <> show err)
      exitFailure
    Right package -> pure package

runChecks :: CertifiedReleaseArtifact -> CertifiedReleasePackage -> IO ()
runChecks release package = do
  let profile = certifiedReleaseProfile release
      llvm = certifiedReleaseLLVMArtifact release
      llvmModule = llvmArtifactModule llvm
      rendered = renderCertifiedReleasePackage package
      targetBoundary = Map.lookup
        (ReleaseTrustBoundaryId "target-assumptions")
        (certifiedReleaseTrustBoundaries release)
      checks =
        [ ( "release profile revision is Darwin-specific"
          , releaseProfileRevision profile
              == ReleaseProfileRevision "phase1.target.aarch64-apple-darwin.v1"
          )
        , ( "release profile selects exact Darwin LLVM target"
          , releaseProfileLLVMTarget profile
              == phase1RuntimeChoiceAArch64AppleDarwinTarget
          )
        , ( "certified LLVM module carries exact Darwin triple and layout"
          , llvmTargetTriple llvmModule == "aarch64-apple-darwin"
              && llvmDataLayout llvmModule == "e-m:o-i64:64-i128:128-n32:64-S128"
              && llvmRuntimeABIProfile llvmModule
                  == "phil-runtime/phase1/runtime-choice-provider-v1"
              && llvmRuntimeABIDigest llvmModule
                  == llvmTargetRuntimeABIDigest phase1RuntimeChoiceAArch64AppleDarwinTarget
          )
        , ( "release retains exactly six residual TCB kinds"
          , Map.size (certifiedReleaseTrustBoundaries release) == 6
              && releaseProfileRequiredTrustKinds profile == Set.fromList
                  [ CompilerCheckerTrust
                  , LLVMToolchainTrust
                  , RuntimeTrust
                  , ProviderTrust
                  , ExternalCheckerTrust
                  , TargetAssumptionTrust
                  ]
          )
        , ( "target trust boundary names Apple Silicon Darwin assumptions"
          , case targetBoundary of
              Just boundary ->
                releaseTrustKind boundary == TargetAssumptionTrust
                  && releaseTrustName boundary
                      == "aarch64 Apple Darwin target assumptions"
                  && releaseTrustRevision boundary
                      == "phase1-aarch64-apple-darwin-v1"
                  && releaseTrustBasis boundary
                      == "selected Apple Silicon Darwin ABI/tool/runtime assumptions"
              Nothing -> False
          )
        , ( "rendered package carries Darwin release identity"
          , Text.isInfixOf
              "release-profile\trevision=phase1.target.aarch64-apple-darwin.v1"
              rendered
              && Text.isInfixOf "target-triple=aarch64-apple-darwin" rendered
              && Text.isInfixOf
                  "data-layout=e-m:o-i64:64-i128:128-n32:64-S128"
                  rendered
              && Text.isInfixOf
                  "name=aarch64 Apple Darwin target assumptions"
                  rendered
              && not (Text.isInfixOf "x86_64 Linux target assumptions" rendered)
          )
        ]
  results <- mapM report checks
  if and results then pure () else exitFailure

report :: (String, Bool) -> IO Bool
report (label, ok) = do
  putStrLn ((if ok then "PASS: " else "FAIL: ")
    <> "TARGET-AARCH64-APPLE-DARWIN " <> label)
  pure ok

certifyDarwinFixture
  :: RealManifestFixture
  -> Either CertifiedReleaseError CertifiedReleaseArtifact
certifyDarwinFixture fixture = certifyReleaseArtifact
  (darwinReleaseProfile manifest)
  (realFixtureContext fixture)
  (realFixtureLedger fixture)
  manifest
  (realFixtureStage fixture)
  (darwinLLVMArtifact fixture)
  darwinTrust
  where
    manifest = realFixtureManifest fixture

darwinReleaseProfile :: AssuranceManifest -> CertifiedReleaseProfile
darwinReleaseProfile manifest = CertifiedReleaseProfile
  { releaseProfileRevision =
      ReleaseProfileRevision "phase1.target.aarch64-apple-darwin.v1"
  , releaseProfileManifestTarget = manifestTarget manifest
  , releaseProfileManifestCompilationProfile = manifestCompilationProfile manifest
  , releaseProfileLLVMTarget = phase1RuntimeChoiceAArch64AppleDarwinTarget
  , releaseProfileRequiredTrustKinds = Set.fromList
      [ CompilerCheckerTrust
      , LLVMToolchainTrust
      , RuntimeTrust
      , ProviderTrust
      , ExternalCheckerTrust
      , TargetAssumptionTrust
      ]
  }

darwinLLVMArtifact :: RealManifestFixture -> LLVMArtifact
darwinLLVMArtifact =
  lowerSystemsConservative phase1RuntimeChoiceAArch64AppleDarwinTarget
    . stageSystemsArtifact
    . realFixtureStage

stageSystemsArtifact :: StageClosureBundle -> SystemsArtifact
stageSystemsArtifact = phase1StageSystemsArtifact
  . subjectStageBase
  . concreteSubjectStage
  . stageClosureConcrete

darwinTrust :: [ReleaseTrustBoundary]
darwinTrust = map specializeTarget conventionalTrust
  where
    specializeTarget boundary
      | releaseTrustKind boundary == TargetAssumptionTrust = boundary
          { releaseTrustName = "aarch64 Apple Darwin target assumptions"
          , releaseTrustRevision = "phase1-aarch64-apple-darwin-v1"
          , releaseTrustBasis =
              "selected Apple Silicon Darwin ABI/tool/runtime assumptions"
          }
      | otherwise = boundary
