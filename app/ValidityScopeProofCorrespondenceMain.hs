{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.Types
import Phil.Assurance.Verify
import Phil.Core.Syntax (ObligationId (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "bound validity-scope fixture verifies" baseFixtureVerifies
    , test "bound target drift rejects evidence reuse" targetDriftRejects
    , test "bound compilation-profile drift rejects evidence reuse" profileDriftRejects
    , test "unbound context-dimension drift preserves scope match" unboundDimensionDriftPasses
    , test "newly bound missing dimension rejects" strengthenedMissingDimensionRejects
    , test "newly bound matching dimension verifies" strengthenedMatchingDimensionPasses
    ]
  if and results then pure () else exitFailure

baseFixtureVerifies :: Bool
baseFixtureVerifies =
  let (ledger, manifest, context) = fixture
  in verifyManifest context ledger manifest == Right ()

targetDriftRejects :: Bool
targetDriftRejects =
  let (ledger, manifest0, context0) = fixture
      manifest = seal ledger manifest0 { manifestTarget = "target-b" }
      context = context0 { verificationTarget = "target-b" }
  in case verifyManifest context ledger manifest of
      Left EvidenceValidityScopeMismatch {} -> True
      _ -> False

profileDriftRejects :: Bool
profileDriftRejects =
  let (ledger, manifest0, context0) = fixture
      manifest = seal ledger manifest0 { manifestCompilationProfile = "profile-b" }
      context = context0 { verificationCompilationProfile = "profile-b" }
  in case verifyManifest context ledger manifest of
      Left EvidenceValidityScopeMismatch {} -> True
      _ -> False

unboundDimensionDriftPasses :: Bool
unboundDimensionDriftPasses =
  let (ledger, manifest0, context0) = fixture
      changed = Map.insert "unbound" "context-b" (manifestValidityContext manifest0)
      manifest = seal ledger manifest0 { manifestValidityContext = changed }
      context = context0 { verificationValidityContext = changed }
  in verifyManifest context ledger manifest == Right ()

strengthenedMissingDimensionRejects :: Bool
strengthenedMissingDimensionRejects =
  let (ledger0, manifest0, context) = fixture
      ledger = adjustScope
        (ValidityScope (Map.fromList
          [ ("target", "target-a")
          , ("compilation_profile", "profile-a")
          , ("provider", "provider-a")
          ]))
        ledger0
      manifest = seal ledger manifest0
  in case verifyManifest context ledger manifest of
      Left EvidenceValidityScopeMismatch {} -> True
      _ -> False

strengthenedMatchingDimensionPasses :: Bool
strengthenedMatchingDimensionPasses =
  let (ledger0, manifest0, context0) = fixture
      ledger = adjustScope
        (ValidityScope (Map.fromList
          [ ("target", "target-a")
          , ("compilation_profile", "profile-a")
          , ("provider", "provider-a")
          ]))
        ledger0
      validity = Map.insert "provider" "provider-a" (manifestValidityContext manifest0)
      manifest = seal ledger manifest0 { manifestValidityContext = validity }
      context = context0 { verificationValidityContext = validity }
  in verifyManifest context ledger manifest == Right ()

fixture :: (AssuranceLedger, AssuranceManifest, VerificationContext)
fixture = (ledger, manifest, context)
  where
    provisionalRevision = ObligationRevision
      { revisionObligationId = ObligationId "test.validity.scope"
      , revisionId = RevisionId ""
      , revisionStatement = "bound validity-scope authority"
      , revisionStatementDigest = digestText "bound validity-scope authority"
      , revisionKind = "ValidityScopeTest"
      , revisionOrigin = "app/ValidityScopeProofCorrespondenceMain.hs"
      , revisionScope = "test.validity.scope"
      , revisionRequiredAt = "certification"
      , revisionRepresentation = "minimal assurance fixture"
      , revisionSubjectIds = []
      , revisionContextIds = []
      , revisionAcceptanceRule = AcceptEntry KernelChecked (EvidenceRole "establishes")
      , revisionGeneratedFrom = []
      }
    revision = provisionalRevision { revisionId = deriveRevisionId provisionalRevision }
    provisionalEvidence = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId "evidence.test.validity.scope"
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = KernelChecked
      , evidenceRole = EvidenceRole "establishes"
      , evidenceProducer = "validity-scope correspondence fixture"
      , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = ValidityScope (Map.fromList
          [ ("target", "target-a")
          , ("compilation_profile", "profile-a")
          ])
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = ["scopeMatches correspondence"]
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }
    evidence = provisionalEvidence
      { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
    ledger = emptyLedger
      { ledgerRevisions = Map.singleton (revisionId revision) revision
      , ledgerEvidence = Map.singleton (evidenceEntryId evidence) evidence
      }
    provisionalManifest = emptyManifest
      { manifestArchitectureDigest = digestText "validity-scope architecture"
      , manifestPhilCoreDigest = digestText "validity-scope core"
      , manifestImplementationDigest = digestText "validity-scope implementation"
      , manifestTarget = "target-a"
      , manifestCompilationProfile = "profile-a"
      , manifestObligationRevisions = Set.singleton (revisionId revision)
      , manifestCertificationScope = Set.singleton (revisionId revision)
      , manifestEvidenceEntries = Set.singleton (evidenceEntryId evidence)
      , manifestLoweringLedgerRoot = digestText "validity-scope lowering root"
      , manifestValidityContext = Map.singleton "unbound" "context-a"
      }
    manifest = seal ledger provisionalManifest
    context = emptyVerificationContext
      { verificationArchitectureDigest = manifestArchitectureDigest manifest
      , verificationPhilCoreDigest = manifestPhilCoreDigest manifest
      , verificationImplementationDigest = manifestImplementationDigest manifest
      , verificationTarget = manifestTarget manifest
      , verificationCompilationProfile = manifestCompilationProfile manifest
      , verificationExpectedObligations = manifestObligationRevisions manifest
      , verificationLoweringLedgerRoot = manifestLoweringLedgerRoot manifest
      , verificationValidityContext = manifestValidityContext manifest
      }

adjustScope :: ValidityScope -> AssuranceLedger -> AssuranceLedger
adjustScope scope ledger =
  ledger { ledgerEvidence = Map.adjust update evidenceId (ledgerEvidence ledger) }
  where
    evidenceId = EvidenceEntryId "evidence.test.validity.scope"
    update entry =
      let changed = entry { evidenceValidityScope = scope }
      in changed { evidenceEntryDigest = deriveEvidenceEntryDigest changed }

seal :: AssuranceLedger -> AssuranceManifest -> AssuranceManifest
seal ledger manifest = manifest { manifestId = deriveManifestId ledger manifest }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
