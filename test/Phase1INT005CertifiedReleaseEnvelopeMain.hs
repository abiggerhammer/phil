{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types
  ( AssuranceLedger
  , AssuranceManifest (..)
  , Digest
  , VerificationContext (..)
  , deriveManifestId
  , digestText
  , emptyLedger
  , emptyManifest
  , emptyVerificationContext
  )
import Phil.Examples.Phase1.StageClosureWitnesses
  ( steveStageClosureBundle
  , uploadStageClosureBundle
  )
import Phil.LLVM.IR
  ( LLVMArtifact (..)
  , LLVMEmissionContract (..)
  , LLVMTargetProfile (..)
  )
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.LLVM.Phase0 (phase0LLVMTarget)
import Phil.Systems.IR
  ( loweringLedgerRoot
  , systemsArtifactDigest
  , systemsArtifactLoweringLedger
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , concreteSubjectStage
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )
import Phil.Verification.CertifiedRelease
import System.Exit (exitFailure)

main :: IO ()
main = do
  uploadStage <- requireStage "Upload" uploadStageClosureBundle
  steveStage <- requireStage "Steve" steveStageClosureBundle
  let upload = releaseFixture "upload" uploadStage
      steve = releaseFixture "steve" steveStage
      results =
        [ test "INT-005 Upload exact certified-release envelope closes"
            (releaseCloses upload)
        , test "INT-005 Steve exact certified-release envelope closes"
            (releaseCloses steve)
        , test "INT-005 emitted LLVM cannot be rebound to another Systems artifact"
            (wrongLLVMSourceRejected upload)
        , test "INT-005 changed lowering lineage cannot hide behind a self-consistent manifest"
            (wrongLoweringRootRejected upload)
        , test "INT-005 canonical emitted LLVM text is release identity"
            (noncanonicalLLVMTextRejected upload)
        , test "INT-005 selected LLVM target profile is exact"
            (wrongLLVMProfileRejected upload)
        , test "INT-005 residual TCB kind omission rejects"
            (missingTrustKindRejected upload)
        , test "INT-005 duplicate residual TCB identity rejects"
            (duplicateTrustIdentityRejected upload)
        , test "INT-005 residual TCB entries must name their trusted basis"
            (blankTrustBasisRejected upload)
        ]
  if and results then pure () else exitFailure

requireStage :: String -> Either String StageClosureBundle -> IO StageClosureBundle
requireStage label result = case result of
  Left detail -> putStrLn ("FAIL: INT-005 " <> label <> " stage fixture -- " <> detail) >> exitFailure
  Right stage -> pure stage

test :: String -> Bool -> Bool
test label result = result `seq` result

report :: String -> Bool -> IO Bool
report label result = do
  putStrLn ((if result then "PASS: " else "FAIL: ") <> label)
  pure result

-- Keep the test declarations pure, but report all controls from main.
-- This wrapper is intentionally separate from the release constructor.
{-# NOINLINE test #-}

releaseCloses :: ReleaseFixture -> Bool
releaseCloses fixture =
  case runRelease fixture of
    Right release ->
      certifiedReleaseManifest release == fixtureManifest fixture
        && certifiedReleaseStageClosure release == fixtureStage fixture
        && certifiedReleaseLLVMArtifact release == fixtureLLVM fixture
        && Map.size (certifiedReleaseTrustBoundaries release) == 6
    Left _ -> False

wrongLLVMSourceRejected :: ReleaseFixture -> Bool
wrongLLVMSourceRejected fixture =
  let artifact = fixtureLLVM fixture
      contract = llvmArtifactContract artifact
      wrongDigest = digestText "int005.unrelated.systems"
      changed = artifact
        { llvmArtifactContract = contract
            { llvmContractSourceDigest = wrongDigest }
        }
      expected = stageSystemsDigest (fixtureStage fixture)
  in case runReleaseWith fixture
      (fixtureContext fixture)
      (fixtureManifest fixture)
      changed
      (fixtureTrust fixture) of
      Left (CertifiedReleaseLLVMSourceDigestMismatch expected' actual') ->
        expected' == expected && actual' == wrongDigest
      _ -> False

wrongLoweringRootRejected :: ReleaseFixture -> Bool
wrongLoweringRootRejected fixture =
  let wrongRoot = digestText "int005.unrelated.lowering-lineage"
      context = (fixtureContext fixture)
        { verificationLoweringLedgerRoot = wrongRoot }
      provisional = (fixtureManifest fixture)
        { manifestId = digestText "pending"
        , manifestLoweringLedgerRoot = wrongRoot
        }
      manifest = provisional
        { manifestId = deriveManifestId fixtureLedger provisional }
      expected = stageLoweringRoot (fixtureStage fixture)
  in case runReleaseWith fixture context manifest
      (fixtureLLVM fixture) (fixtureTrust fixture) of
      Left (CertifiedReleaseManifestLoweringLedgerRootMismatch expected' actual') ->
        expected' == expected && actual' == wrongRoot
      _ -> False

noncanonicalLLVMTextRejected :: ReleaseFixture -> Bool
noncanonicalLLVMTextRejected fixture =
  let artifact = fixtureLLVM fixture
      changed = artifact
        { llvmArtifactText = llvmArtifactText artifact <> "; not canonical\n" }
  in case runReleaseWith fixture
      (fixtureContext fixture)
      (fixtureManifest fixture)
      changed
      (fixtureTrust fixture) of
      Left CertifiedReleaseLLVMTextMismatch -> True
      _ -> False

wrongLLVMProfileRejected :: ReleaseFixture -> Bool
wrongLLVMProfileRejected fixture =
  let expected = releaseProfileLLVMTarget (fixtureProfile fixture)
      changedTarget = expected
        { llvmTargetTripleName = "aarch64-unknown-linux-gnu" }
      profile = (fixtureProfile fixture)
        { releaseProfileLLVMTarget = changedTarget }
  in case certifyReleaseArtifact
      profile
      (fixtureContext fixture)
      (fixtureLedger fixture)
      (fixtureManifest fixture)
      (fixtureStage fixture)
      (fixtureLLVM fixture)
      (fixtureTrust fixture) of
      Left (CertifiedReleaseLLVMTargetProfileMismatch expected' actual') ->
        expected' == changedTarget && actual' == expected
      _ -> False

missingTrustKindRejected :: ReleaseFixture -> Bool
missingTrustKindRejected fixture =
  let reduced = filter
        ((/= TargetAssumptionTrust) . releaseTrustKind)
        (fixtureTrust fixture)
      expected = releaseProfileRequiredTrustKinds (fixtureProfile fixture)
      actual = Set.delete TargetAssumptionTrust expected
  in case runReleaseWith fixture
      (fixtureContext fixture)
      (fixtureManifest fixture)
      (fixtureLLVM fixture)
      reduced of
      Left (CertifiedReleaseTrustKindDomainMismatch expected' actual') ->
        expected' == expected && actual' == actual
      _ -> False

duplicateTrustIdentityRejected :: ReleaseFixture -> Bool
duplicateTrustIdentityRejected fixture =
  case fixtureTrust fixture of
    [] -> False
    first : _ ->
      case runReleaseWith fixture
          (fixtureContext fixture)
          (fixtureManifest fixture)
          (fixtureLLVM fixture)
          (fixtureTrust fixture <> [first]) of
        Left (CertifiedReleaseDuplicateTrustBoundary duplicateId) ->
          duplicateId == releaseTrustBoundaryId first
        _ -> False

blankTrustBasisRejected :: ReleaseFixture -> Bool
blankTrustBasisRejected fixture =
  case fixtureTrust fixture of
    [] -> False
    first : rest ->
      let changed = first { releaseTrustBasis = "   " }
      in case runReleaseWith fixture
          (fixtureContext fixture)
          (fixtureManifest fixture)
          (fixtureLLVM fixture)
          (changed : rest) of
          Left (CertifiedReleaseEmptyTrustBasis boundaryId) ->
            boundaryId == releaseTrustBoundaryId first
          _ -> False

data ReleaseFixture = ReleaseFixture
  { fixtureProfile :: CertifiedReleaseProfile
  , fixtureContext :: VerificationContext
  , fixtureLedger :: AssuranceLedger
  , fixtureManifest :: AssuranceManifest
  , fixtureStage :: StageClosureBundle
  , fixtureLLVM :: LLVMArtifact
  , fixtureTrust :: [ReleaseTrustBoundary]
  }

releaseFixture :: Text -> StageClosureBundle -> ReleaseFixture
releaseFixture witness stage = ReleaseFixture
  { fixtureProfile = releaseProfile
  , fixtureContext = context
  , fixtureLedger = ledger
  , fixtureManifest = manifest
  , fixtureStage = stage
  , fixtureLLVM = llvm
  , fixtureTrust = conventionalTrust
  }
  where
    ledger = emptyLedger
    systems = stageSystemsArtifact stage
    systemsDigest = systemsArtifactDigest systems
    root = loweringLedgerRoot (systemsArtifactLoweringLedger systems)
    targetName = "phase1-conventional-x86_64-linux"
    compilationProfile = "phase1/int005/certified-release-envelope-v1"
    architectureDigest = digestText ("int005.architecture." <> witness)
    coreDigest = digestText ("int005.core." <> witness)
    context = emptyVerificationContext
      { verificationArchitectureDigest = architectureDigest
      , verificationPhilCoreDigest = coreDigest
      , verificationImplementationDigest = systemsDigest
      , verificationTarget = targetName
      , verificationCompilationProfile = compilationProfile
      , verificationLoweringLedgerRoot = root
      }
    provisional = emptyManifest
      { manifestArchitectureDigest = architectureDigest
      , manifestPhilCoreDigest = coreDigest
      , manifestImplementationDigest = systemsDigest
      , manifestTarget = targetName
      , manifestCompilationProfile = compilationProfile
      , manifestLoweringLedgerRoot = root
      }
    manifest = provisional
      { manifestId = deriveManifestId ledger provisional }
    llvm = lowerSystemsConservative phase0LLVMTarget systems
    releaseProfile = CertifiedReleaseProfile
      { releaseProfileRevision =
          ReleaseProfileRevision "phase1.int005.conventional-x86_64-linux.v1"
      , releaseProfileManifestTarget = targetName
      , releaseProfileManifestCompilationProfile = compilationProfile
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

runRelease :: ReleaseFixture -> Either CertifiedReleaseError CertifiedReleaseArtifact
runRelease fixture = runReleaseWith fixture
  (fixtureContext fixture)
  (fixtureManifest fixture)
  (fixtureLLVM fixture)
  (fixtureTrust fixture)

runReleaseWith
  :: ReleaseFixture
  -> VerificationContext
  -> AssuranceManifest
  -> LLVMArtifact
  -> [ReleaseTrustBoundary]
  -> Either CertifiedReleaseError CertifiedReleaseArtifact
runReleaseWith fixture context manifest artifact trust = certifyReleaseArtifact
  (fixtureProfile fixture)
  context
  (fixtureLedger fixture)
  manifest
  (fixtureStage fixture)
  artifact
  trust

stageSystemsArtifact stage =
  phase1StageSystemsArtifact
    . subjectStageBase
    . concreteSubjectStage
    . stageClosureConcrete
    $ stage

stageSystemsDigest :: StageClosureBundle -> Digest
stageSystemsDigest = systemsArtifactDigest . stageSystemsArtifact

stageLoweringRoot :: StageClosureBundle -> Digest
stageLoweringRoot =
  loweringLedgerRoot . systemsArtifactLoweringLedger . stageSystemsArtifact

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
