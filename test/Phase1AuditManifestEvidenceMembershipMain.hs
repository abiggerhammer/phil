{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.Types
import Phil.Core.Syntax (Obligation (Obligation), ObligationId (..), Proposition (Truth))
import Phil.Verification
import Phil.Verification.Bundle
import Phil.Verification.ManifestClosure
import System.Exit (exitFailure)

data Fixture = Fixture
  { fixtureBundle :: VerificationBundle
  , fixturePolicy :: ApplicationAssurancePolicy
  , fixtureContext :: VerificationContext
  , fixtureLedger :: AssuranceLedger
  , fixtureSelection :: ManifestClosureSelection
  }

firstId, secondId :: EvidenceEntryId
firstId = EvidenceEntryId "audit.handoff.first"
secondId = EvidenceEntryId "audit.handoff.second"

obligationId :: ObligationId
obligationId = ObligationId "audit.handoff.obligation"

main :: IO ()
main = do
  results <- sequence
    [ test "R01 empty bundle cannot select valid static ledger evidence"
        (membershipRejects KernelChecked [] firstId)
    , test "R02 bundle evidence A cannot authorize selected evidence B"
        (membershipRejects KernelChecked [firstId] secondId)
    , test "R03 empty bundle cannot select valid runtime ledger evidence"
        (membershipRejects RuntimeEnforced [] firstId)
    , test "C01 listed static evidence closes"
        (fixture KernelChecked [firstId] [firstId] >>= closes)
    , test "C02 listed runtime evidence closes"
        (fixture RuntimeEnforced [firstId] [firstId] >>= closes)
    , test "C03 selecting first member of larger bundle closes"
        (fixture KernelChecked [firstId, secondId] [firstId] >>= closes)
    , test "C04 selecting second member of larger bundle closes"
        (fixture KernelChecked [firstId, secondId] [secondId] >>= closes)
    , test "C05 unselected extra ledger evidence remains harmless"
        (fixture KernelChecked [firstId] [firstId] >>= closes)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: PHIL-AUD-MANIFEST-EVIDENCE-MEMBERSHIP-001 " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: PHIL-AUD-MANIFEST-EVIDENCE-MEMBERSHIP-001 " <> label <> " -- " <> detail) >> pure False

membershipRejects
  :: AssuranceKind
  -> [EvidenceEntryId]
  -> EvidenceEntryId
  -> Either String ()
membershipRejects kind listed selected = do
  fixtureValue <- fixture kind listed [selected]
  case close fixtureValue of
    Left (ManifestClosureAcceptedEvidenceMissing actual)
      | actual == selected -> Right ()
    other -> Left ("expected selected evidence to be absent from bundle, got " <> show other)

closes :: Fixture -> Either String ()
closes fixtureValue =
  case close fixtureValue of
    Right manifest
      | manifestEvidenceEntries manifest
          == manifestClosureEvidence (fixtureSelection fixtureValue) -> Right ()
      | otherwise -> Left "accepted manifest changed selected evidence set"
    Left err -> Left ("expected closure acceptance, got " <> show err)

close :: Fixture -> Either ManifestClosureError AssuranceManifest
close fixtureValue =
  closeVerificationBundle
    (fixtureBundle fixtureValue)
    (fixturePolicy fixtureValue)
    (fixtureContext fixtureValue)
    (fixtureLedger fixtureValue)
    (fixtureSelection fixtureValue)

fixture
  :: AssuranceKind
  -> [EvidenceEntryId]
  -> [EvidenceEntryId]
  -> Either String Fixture
fixture kind listed selected = do
  graph <- mapLeft show $
    buildVerificationObligationGraph
      [obligationInput kind]
      (Set.singleton obligationId)
  revision <- revisionFor graph
  let entries = Map.fromList
        [ (firstId, evidenceFor kind revision firstId)
        , (secondId, evidenceFor kind revision secondId)
        ]
  listedEntries <- mapM
    (\entryId -> maybe (Left "unknown fixture evidence id") Right
      (Map.lookup entryId entries))
    listed
  bundle <- mapLeft show $
    buildVerificationBundle
      (digestText "audit.handoff.source")
      [] [] []
      graph
      policy
      listedEntries
  let context = emptyVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = digestText "audit.core"
        , verificationImplementationDigest = digestText "audit.implementation"
        , verificationTarget = "audit-target"
        , verificationCompilationProfile = "checked-runtime"
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , verificationLoweringLedgerRoot = digestText "audit.lowering"
        , verificationKnownCostRefs = Set.singleton "audit.cost"
        }
      ledger = emptyLedger
        { ledgerRevisions = verificationGraphNodes graph
        , ledgerEvidence = entries
        }
      selection = ManifestClosureSelection
        { manifestClosureEvidence = Set.fromList selected
        , manifestClosureAssumptions = Set.empty
        , manifestClosureExports = Map.empty
        , manifestClosureUses = Set.empty
        }
  Right Fixture
    { fixtureBundle = bundle
    , fixturePolicy = policy
    , fixtureContext = context
    , fixtureLedger = ledger
    , fixtureSelection = selection
    }

policy :: ApplicationAssurancePolicy
policy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "audit.handoff.policy.v1"
  , applicationAssurancePolicyPermittedDispositions =
      Set.fromList [StaticallyDischarged, RuntimeBound]
  }

obligationInput :: AssuranceKind -> VerificationObligationInput
obligationInput kind = VerificationObligationInput
  { verificationInputObligation = Obligation
      obligationId
      Truth
      "assurance handoff audit"
      "audit.component"
      "before closure"
  , verificationInputKind = "AuditControl"
  , verificationInputRepresentation = "Core"
  , verificationInputSubjectIds = []
  , verificationInputContextIds = []
  , verificationInputAcceptanceRule = AcceptEntry kind (EvidenceRole "establishes")
  , verificationInputDependencies = Set.empty
  }

revisionFor :: VerificationObligationGraph -> Either String ObligationRevision
revisionFor graph =
  case Map.elems (verificationGraphNodes graph) of
    [revision] -> Right revision
    other -> Left ("expected one revision, got " <> show other)

evidenceFor
  :: AssuranceKind
  -> ObligationRevision
  -> EvidenceEntryId
  -> EvidenceEntry
evidenceFor kind revision entryId = sealed
  where
    raw = EvidenceEntry
      { evidenceEntryId = entryId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = kind
      , evidenceRole = EvidenceRole "establishes"
      , evidenceProducer = unEvidenceEntryId entryId
      , evidenceChecker = "audit fixture"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = ValidityScope Map.empty
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = ["true"]
      , evidenceRuntimeMechanism =
          if kind == RuntimeEnforced
            then Just RuntimeMechanism
              { runtimeMechanismName = "declared-truth-check"
              , runtimeExecutionPoint = "before closure"
              , runtimeSuccessEvidenceType = "Proof[true]"
              , runtimeFailureContract = "reject without continuation"
              , runtimeImplementation = Nothing
              }
            else Nothing
      , evidenceRuntimeResidue =
          if kind == RuntimeEnforced then ["retain declared check"] else []
      , evidenceCostRefs =
          if kind == RuntimeEnforced then ["audit.cost"] else []
      }
    sealed = raw { evidenceEntryDigest = deriveEvidenceEntryDigest raw }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
