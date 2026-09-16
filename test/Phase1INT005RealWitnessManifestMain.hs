{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types
  ( AssuranceManifest (..)
  )
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.LLVM.Phase0 (phase0LLVMTarget)
import Phil.Systems.IR (SystemsArtifact)
import Phil.Systems.Phase1Stage (phase1StageSystemsArtifact)
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , concreteSubjectStage
  )
import Phil.Systems.SubjectCorrespondence (SubjectStageBundle (..))
import Phil.Test.Phase1.ManifestWitnesses
import Phil.Verification.CertifiedRelease
import System.Exit (exitFailure)

main :: IO ()
main = do
  uploadClient <- TextIO.readFile "examples/upload/client.phil"
  uploadServer <- TextIO.readFile "examples/upload/server.phil"
  stevePut <- TextIO.readFile "examples/steve/put.phil"
  steveGet <- TextIO.readFile "examples/steve/get.phil"
  let fixtures =
        [ ("Upload", uploadRealManifestFixture uploadClient uploadServer)
        , ("Steve", steveRealManifestFixture stevePut steveGet)
        ]
  results <- mapM runFixture fixtures
  if and results then pure () else exitFailure

runFixture :: (String, Either String RealManifestFixture) -> IO Bool
runFixture (label, result) = case result of
  Left detail -> do
    putStrLn ("FAIL: INT-005 " <> label <> " real manifest fixture -- " <> detail)
    pure False
  Right fixture -> report label (certifyFixture fixture)

report :: String -> Bool -> IO Bool
report label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ")
    <> "INT-005 " <> label <> " real ordinary-source manifest certifies exact release envelope")
  pure ok

certifyFixture :: RealManifestFixture -> Bool
certifyFixture fixture =
  case certifyReleaseArtifact
      profile
      (realFixtureContext fixture)
      (realFixtureLedger fixture)
      manifest
      stage
      llvm
      conventionalTrust of
    Right certified ->
      certifiedReleaseManifest certified == manifest
        && certifiedReleaseStageClosure certified == stage
        && certifiedReleaseLLVMArtifact certified == llvm
        && certifiedReleaseProfile certified == profile
        && Map.size (certifiedReleaseTrustBoundaries certified) == 6
    Left _ -> False
  where
    manifest = realFixtureManifest fixture
    stage = realFixtureStage fixture
    systems = stageSystemsArtifact stage
    llvm = lowerSystemsConservative phase0LLVMTarget systems
    profile = CertifiedReleaseProfile
      { releaseProfileRevision = ReleaseProfileRevision
          "phase1.int005.real-witness-manifest-envelope.v1"
      , releaseProfileManifestTarget = manifestTarget manifest
      , releaseProfileManifestCompilationProfile = manifestCompilationProfile manifest
      , releaseProfileLLVMTarget = phase0LLVMTarget
      , releaseProfileRequiredTrustKinds = Set.fromList
          [ CompilerCheckerTrust
          , LLVMToolchainTrust
          , RuntimeTrust
          , ProviderTrust
          , ExternalCheckerTrust
          , TargetAssumptionTrust
          ]
      }

stageSystemsArtifact :: StageClosureBundle -> SystemsArtifact
stageSystemsArtifact = phase1StageSystemsArtifact
  . subjectStageBase
  . concreteSubjectStage
  . stageClosureConcrete

conventionalTrust :: [ReleaseTrustBoundary]
conventionalTrust =
  [ trust "compiler-checker" CompilerCheckerTrust
      "Phil Haskell compiler/checker" "phase1-current"
      "first implementation remains trusted until Phase 2"
  , trust "llvm-toolchain" LLVMToolchainTrust
      "LLVM assembler/linker and clang" "LLVM 18.x"
      "conventional native emission and link toolchain"
  , trust "runtime" RuntimeTrust
      "Phil conventional host runtime" "phase1-runtime-v1"
      "runtime behavior below checked Phil/Systems contracts"
  , trust "providers" ProviderTrust
      "qualified conventional providers" "phase1-provider-set-v1"
      "provider implementations remain trusted at their declared qualification boundaries"
  , trust "external-checkers" ExternalCheckerTrust
      "external proof/certificate checkers" "phase1-certified-checker-set-v1"
      "accepted external evidence depends on the named competent checkers"
  , trust "target-assumptions" TargetAssumptionTrust
      "x86_64 Linux target assumptions" "phase1-x86_64-linux-v1"
      "selected conventional ABI/tool/runtime assumptions"
  ]
  where
    trust ident kind name revision basis = ReleaseTrustBoundary
      { releaseTrustBoundaryId = ReleaseTrustBoundaryId ident
      , releaseTrustKind = kind
      , releaseTrustName = name
      , releaseTrustRevision = revision
      , releaseTrustBasis = basis
      }
