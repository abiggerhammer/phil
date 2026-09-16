{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Assurance.Verify (verifyManifest)
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (Truth)
  )
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
  , fixtureRuntimeEvidenceId :: EvidenceEntryId
  , fixtureAssumptionId :: AssumptionId
  , fixtureExportId :: ExportId
  }

main :: IO ()
main = do
  results <- sequence
    [ test "INT-002 generic bundle-to-manifest closure accepts explicit static/runtime/assumption/export dispositions"
        happyPath
    , test "INT-002 RuntimeBound must be explicitly permitted by the selected policy"
        runtimePolicyMustBeExplicit
    , test "INT-002 evidence assumption dependencies cannot be silently omitted"
        assumptionDependencyMustBeSelected
    , test "INT-002 export disposition is explicit rather than inferred from an ExportEntry"
        exportDispositionMustBeExplicit
    , test "INT-002 accepted VerificationBundle evidence is exact against the assurance ledger"
        bundleEvidenceDriftRejected
    , test "INT-002 bundle policy revision cannot be replaced during manifest closure"
        policyRevisionMustMatchBundle
    , test "INT-002 VerificationBundle owns the exact manifest obligation domain"
        obligationDomainCannotDrift
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

happyPath :: Either String ()
happyPath = do
  fixture <- baseFixture basePolicy
  manifest <- mapLeft show (closeFixture fixture)
  mapLeft show
    (verifyManifest (fixtureContext fixture) (fixtureLedger fixture) manifest)

runtimePolicyMustBeExplicit :: Either String ()
runtimePolicyMustBeExplicit = do
  let policy = basePolicy
        { applicationAssurancePolicyPermittedDispositions = Set.fromList
            [StaticallyDischarged, AssumptionDependent, Exported]
        }
  fixture <- baseFixture policy
  case closeFixture fixture of
    Left (ManifestClosureUnpermittedDisposition RuntimeBound) -> Right ()
    other -> Left ("expected RuntimeBound policy rejection, got " <> show other)

assumptionDependencyMustBeSelected :: Either String ()
assumptionDependencyMustBeSelected = do
  fixture <- baseFixture basePolicy
  let selection = (fixtureSelection fixture)
        { manifestClosureAssumptions = Set.empty }
      expectedEvidence = fixtureRuntimeEvidenceId fixture
      expectedAssumption = fixtureAssumptionId fixture
  case closeVerificationBundle
      (fixtureBundle fixture)
      (fixturePolicy fixture)
      (fixtureContext fixture)
      (fixtureLedger fixture)
      selection of
    Left (ManifestClosureMissingSelectedAssumptionDependency entryId assumptionKey)
      | entryId == expectedEvidence && assumptionKey == expectedAssumption -> Right ()
    other -> Left ("expected explicit assumption-dependency rejection, got " <> show other)

exportDispositionMustBeExplicit :: Either String ()
exportDispositionMustBeExplicit = do
  fixture <- baseFixture basePolicy
  let exportKey = fixtureExportId fixture
      selection = (fixtureSelection fixture)
        { manifestClosureExports = Map.singleton exportKey RuntimeBound }
  case closeVerificationBundle
      (fixtureBundle fixture)
      (fixturePolicy fixture)
      (fixtureContext fixture)
      (fixtureLedger fixture)
      selection of
    Left (ManifestClosureInvalidExportDisposition actual RuntimeBound)
      | actual == exportKey -> Right ()
    other -> Left ("expected explicit export-disposition rejection, got " <> show other)

bundleEvidenceDriftRejected :: Either String ()
bundleEvidenceDriftRejected = do
  fixture <- baseFixture basePolicy
  let entryId = fixtureRuntimeEvidenceId fixture
      ledger0 = fixtureLedger fixture
      evidence0 = ledgerEvidence ledger0 Map.! entryId
      evidence1 = evidence0 { evidenceEntryDigest = digestText "tampered" }
      ledger1 = ledger0
        { ledgerEvidence = Map.insert entryId evidence1 (ledgerEvidence ledger0) }
  case closeVerificationBundle
      (fixtureBundle fixture)
      (fixturePolicy fixture)
      (fixtureContext fixture)
      ledger1
      (fixtureSelection fixture) of
    Left (ManifestClosureAcceptedEvidenceMismatch actual)
      | actual == entryId -> Right ()
    other -> Left ("expected bundle/ledger evidence mismatch, got " <> show other)

policyRevisionMustMatchBundle :: Either String ()
policyRevisionMustMatchBundle = do
  fixture <- baseFixture basePolicy
  let replacement = (fixturePolicy fixture)
        { applicationAssurancePolicyRevision = AssurancePolicyRevision "different-policy" }
  case closeVerificationBundle
      (fixtureBundle fixture)
      replacement
      (fixtureContext fixture)
      (fixtureLedger fixture)
      (fixtureSelection fixture) of
    Left ManifestClosurePolicyRevisionMismatch {} -> Right ()
    other -> Left ("expected policy-revision mismatch, got " <> show other)

obligationDomainCannotDrift :: Either String ()
obligationDomainCannotDrift = do
  fixture <- baseFixture basePolicy
  let context0 = fixtureContext fixture
      context1 = context0 { verificationExpectedObligations = Set.empty }
  case closeVerificationBundle
      (fixtureBundle fixture)
      (fixturePolicy fixture)
      context1
      (fixtureLedger fixture)
      (fixtureSelection fixture) of
    Left ManifestClosureExpectedObligationsMismatch {} -> Right ()
    other -> Left ("expected exact obligation-domain rejection, got " <> show other)

closeFixture :: Fixture -> Either ManifestClosureError AssuranceManifest
closeFixture fixture = closeVerificationBundle
  (fixtureBundle fixture)
  (fixturePolicy fixture)
  (fixtureContext fixture)
  (fixtureLedger fixture)
  (fixtureSelection fixture)

basePolicy :: ApplicationAssurancePolicy
basePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "int002-policy-v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ StaticallyDischarged
      , RuntimeBound
      , AssumptionDependent
      , Exported
      ]
  }

baseFixture :: ApplicationAssurancePolicy -> Either String Fixture
baseFixture policy = do
  graph <- mapLeft show $ buildVerificationObligationGraph
    [ staticInput, runtimeInput, exportedInput ]
    (Set.fromList [staticId, runtimeId])
  staticRevision <- revisionFor staticId graph
  runtimeRevision <- revisionFor runtimeId graph
  exportedRevision <- revisionFor exportedId graph
  let assumption = mkAssumption
      staticEvidence = mkStaticEvidence staticRevision
      runtimeEvidence = mkRuntimeEvidence runtimeRevision assumption
      exportEntry = mkExport exportedRevision
      ledger = emptyLedger
        { ledgerRevisions = verificationGraphNodes graph
        , ledgerEvidence = Map.fromList
            [ (evidenceEntryId staticEvidence, staticEvidence)
            , (evidenceEntryId runtimeEvidence, runtimeEvidence)
            ]
        , ledgerAssumptions = Map.singleton (assumptionId assumption) assumption
        , ledgerExports = Map.singleton (exportId exportEntry) exportEntry
        }
  bundle <- mapLeft show $ buildVerificationBundle
    (digestText "int002-source")
    [] [] []
    graph
    policy
    [staticEvidence, runtimeEvidence]
  let context = emptyVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = digestText "int002-core"
        , verificationImplementationDigest = digestText "int002-implementation"
        , verificationTarget = "int002-test-target"
        , verificationCompilationProfile = "checked-runtime"
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , verificationPermittedAssumptions = Set.singleton (assumptionId assumption)
        , verificationPermittedExportBoundaries = Set.singleton "phase2"
        , verificationLoweringLedgerRoot = digestText "int002-lowering-root"
        , verificationKnownCostRefs = Set.singleton runtimeCostRef
        , verificationValidityContext = Map.empty
        }
      selection = ManifestClosureSelection
        { manifestClosureEvidence = Set.fromList
            [evidenceEntryId staticEvidence, evidenceEntryId runtimeEvidence]
        , manifestClosureAssumptions = Set.singleton (assumptionId assumption)
        , manifestClosureExports = Map.singleton (exportId exportEntry) Exported
        , manifestClosureUses = Set.empty
        }
  Right Fixture
    { fixtureBundle = bundle
    , fixturePolicy = policy
    , fixtureContext = context
    , fixtureLedger = ledger
    , fixtureSelection = selection
    , fixtureRuntimeEvidenceId = evidenceEntryId runtimeEvidence
    , fixtureAssumptionId = assumptionId assumption
    , fixtureExportId = exportId exportEntry
    }

staticId, runtimeId, exportedId :: ObligationId
staticId = ObligationId "int002.static"
runtimeId = ObligationId "int002.runtime"
exportedId = ObligationId "int002.exported"

staticInput, runtimeInput, exportedInput :: VerificationObligationInput
staticInput = obligationInput staticId
  (AcceptEntry KernelChecked (EvidenceRole "static"))
runtimeInput = obligationInput runtimeId
  (AcceptEntry RuntimeEnforced (EvidenceRole "runtime"))
exportedInput = obligationInput exportedId
  (AcceptEntry KernelChecked (EvidenceRole "external"))

obligationInput :: ObligationId -> AcceptanceRule -> VerificationObligationInput
obligationInput obligationKey acceptance = VerificationObligationInput
  { verificationInputObligation = Obligation
      { obligationId = obligationKey
      , obligationProposition = Truth
      , obligationOrigin = "INT-002 fixture"
      , obligationScope = "int002.fixture"
      , obligationRequiredPoint = "manifest-closure"
      }
  , verificationInputKind = "INT-002"
  , verificationInputRepresentation = "portable verification obligation"
  , verificationInputSubjectIds = []
  , verificationInputContextIds = []
  , verificationInputAcceptanceRule = acceptance
  , verificationInputDependencies = Set.empty
  }

revisionFor :: ObligationId -> VerificationObligationGraph -> Either String ObligationRevision
revisionFor obligationKey graph =
  case filter ((== obligationKey) . revisionObligationId)
      (Map.elems (verificationGraphNodes graph)) of
    [revision] -> Right revision
    revisions -> Left
      ("expected exactly one revision for " <> show obligationKey <> ", got " <> show revisions)

mkAssumption :: Assumption
mkAssumption = provisional { assumptionDigest = deriveAssumptionDigest provisional }
  where
    provisional = Assumption
      { assumptionId = AssumptionId "int002.runtime.assumption"
      , assumptionDigest = Digest ""
      , assumptionStatement = "selected runtime mechanism satisfies its declared contract"
      , assumptionScope = "int002.fixture"
      , assumptionOwnerBoundary = "runtime"
      , assumptionRationale = "explicit INT-002 fixture TCB boundary"
      , assumptionValidityScope = ValidityScope Map.empty
      }

mkStaticEvidence :: ObligationRevision -> EvidenceEntry
mkStaticEvidence revision = sealEvidence EvidenceEntry
  { evidenceEntryId = EvidenceEntryId "int002.static.evidence"
  , evidenceEntryDigest = Digest ""
  , evidenceObligationRevision = revisionId revision
  , evidenceAssuranceKind = KernelChecked
  , evidenceRole = EvidenceRole "static"
  , evidenceProducer = "INT-002 fixture"
  , evidenceChecker = "Phil Core"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = []
  , evidenceDependsOn = []
  , evidenceValidityScope = ValidityScope Map.empty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["static fixture obligation"]
  , evidenceRuntimeMechanism = Nothing
  , evidenceRuntimeResidue = []
  , evidenceCostRefs = []
  }

runtimeCostRef :: Text
runtimeCostRef = "int002.runtime.cost"

mkRuntimeEvidence :: ObligationRevision -> Assumption -> EvidenceEntry
mkRuntimeEvidence revision assumption = sealEvidence EvidenceEntry
  { evidenceEntryId = EvidenceEntryId "int002.runtime.evidence"
  , evidenceEntryDigest = Digest ""
  , evidenceObligationRevision = revisionId revision
  , evidenceAssuranceKind = RuntimeEnforced
  , evidenceRole = EvidenceRole "runtime"
  , evidenceProducer = "INT-002 fixture runtime plan"
  , evidenceChecker = "declared runtime boundary"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = [assumptionId assumption]
  , evidenceDependsOn = []
  , evidenceValidityScope = ValidityScope Map.empty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["runtime fixture obligation"]
  , evidenceRuntimeMechanism = Just RuntimeMechanism
      { runtimeMechanismName = "int002-runtime-check"
      , runtimeExecutionPoint = "fixture boundary"
      , runtimeSuccessEvidenceType = "Validated[INT002]"
      , runtimeFailureContract = "reject without continuing"
      , runtimeImplementation = Nothing
      }
  , evidenceRuntimeResidue = ["runtime check retained"]
  , evidenceCostRefs = [runtimeCostRef]
  }

sealEvidence :: EvidenceEntry -> EvidenceEntry
sealEvidence entry = entry { evidenceEntryDigest = deriveEvidenceEntryDigest entry }

mkExport :: ObligationRevision -> ExportEntry
mkExport revision = provisional { exportDigest = deriveExportDigest provisional }
  where
    provisional = ExportEntry
      { exportId = ExportId "int002.export"
      , exportDigest = Digest ""
      , exportObligationRevision = revisionId revision
      , exportDestinationBoundary = "phase2"
      , exportDerivedObligationId = ObligationId "int002.exported.phase2"
      , exportValidityScope = ValidityScope Map.empty
      }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
