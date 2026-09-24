{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Phil.Assurance.Handoff as Handoff
import qualified Phil.Assurance.Types as Assurance
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import qualified Phil.Core.Discharge as Discharge
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (Unrestricted)
  , Name (..)
  , Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefSort (SortNat)
  , RefTerm (..)
  , Ty (..)
  )
import qualified Phil.Verification as Verification
import qualified Phil.Verification.Bundle as Bundle
import qualified Phil.Verification.ManifestClosure as Closure
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "R01 full-scope definitional result retains its runtime prerequisite"
        fullScopeDefinitionAccepted
    , test "R02 local definitional result cannot export its retained prerequisite"
        exportedDefinitionSupportRejected
    ]
  unless (and results) exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

right :: Show error => Either error value -> Either String value
right = either (Left . show) Right

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False message = Left message

var :: Text -> RefTerm
var = RefVar . Name

sideCondition :: Proposition
sideCondition = LessEqual (var "b") (var "a")

definitionalGoal :: Proposition
definitionalGoal = Equal difference difference
  where
    difference = RefSub (var "a") (var "b")

rootId :: ObligationId
rootId = ObligationId "audit.final-operation-support.root"

childId :: ObligationId
childId = ObligationId "audit.final-operation-support.root.nat-sub.1"

parentEvidenceId :: Assurance.EvidenceEntryId
parentEvidenceId = Assurance.EvidenceEntryId "audit.final-operation-support.parent"

runtimeEvidenceId :: Assurance.EvidenceEntryId
runtimeEvidenceId = Assurance.EvidenceEntryId "audit.final-operation-support.runtime"

childExportId :: Assurance.ExportId
childExportId = Assurance.ExportId "audit.final-operation-support.export.child"

exportBoundary :: Text
exportBoundary = "audit.final-operation-support.external-boundary"

runtimeCost :: Text
runtimeCost = "audit.final-operation-support.cost"

rootObligation :: Obligation
rootObligation = Obligation
  { obligationId = rootId
  , obligationProposition = definitionalGoal
  , obligationOrigin = "Phase1AuditFinalOperationSupportMain"
  , obligationScope = "audit.final-operation-support"
  , obligationRequiredPoint = "before-consumer"
  }

childObligation :: Obligation
childObligation = rootObligation
  { obligationId = childId
  , obligationProposition = sideCondition
  }

natState :: Either String CheckState
natState = foldM add emptyCheckState ["a", "b"]
  where
    add state spelling = do
      context <- right $ insertBinding Unrestricted (Name spelling)
        (TyOpaqueSorted "AuditNat" SortNat) (resourceContext state)
      Right state { resourceContext = context }

runtimeBinding :: Discharge.RuntimeBinding
runtimeBinding = Discharge.RuntimeBinding
  { Discharge.runtimeObligationId = childId
  , Discharge.runtimeProposition = sideCondition
  , Discharge.runtimeRequiredPoint = obligationRequiredPoint childObligation
  , Discharge.runtimeValidator = "declared-order-validator"
  , Discharge.runtimeSuccessEvidence = TyProof sideCondition
  , Discharge.runtimeFailureClass = "ValidationFailure"
  , Discharge.runtimeResourceContract = "preserve unrelated resources; no continuation on failure"
  , Discharge.runtimeCostRef = runtimeCost
  }

resolveDefinition :: Either String Discharge.ResolvedObligation
resolveDefinition = do
  state <- natState
  policy <- right $ Discharge.bindRuntime runtimeBinding Discharge.emptyDischargePolicy
  resolved <- right $
    Discharge.resolveObligation emptyStaticContext state policy rootObligation
  ensure (Discharge.resolvedObligation resolved == rootObligation)
    "resolver changed the original obligation"
  case Discharge.resolvedDisposition resolved of
    Discharge.StaticallyDischarged Discharge.StaticByDefinition -> Right ()
    other -> Left ("expected StaticByDefinition parent, got " <> show other)
  case Discharge.resolvedPrerequisites resolved of
    [child] -> do
      ensure (Discharge.resolvedObligation child == childObligation)
        "resolver changed the retained prerequisite"
      ensure (Discharge.resolvedDisposition child == Discharge.RuntimeBound runtimeBinding)
        "retained prerequisite lost its runtime disposition"
    other -> Left ("expected exactly one retained prerequisite, got " <> show other)
  Right resolved

handoffConfig :: Handoff.HandoffConfig
handoffConfig = Handoff.HandoffConfig
  { Handoff.handoffRevisionKind = const "AuditFinalOperationSupport"
  , Handoff.handoffRepresentation = const "Core"
  , Handoff.handoffSubjectIds = const ["audit:a", "audit:b"]
  , Handoff.handoffContextIds = const ["audit:context"]
  , Handoff.handoffAcceptanceRule = \obligation ->
      if obligationId obligation == childId
        then Assurance.AcceptEntry Assurance.RuntimeEnforced
          (Assurance.EvidenceRole "runtime")
        else Assurance.AcceptEntry Assurance.KernelChecked
          (Assurance.EvidenceRole "establishes")
  }

sealEvidence :: Assurance.EvidenceEntry -> Assurance.EvidenceEntry
sealEvidence entry = entry
  { Assurance.evidenceEntryDigest = Assurance.deriveEvidenceEntryDigest entry }

baseEvidence :: Assurance.RevisionId -> Assurance.EvidenceEntry
baseEvidence revision = Assurance.EvidenceEntry
  { Assurance.evidenceEntryId = parentEvidenceId
  , Assurance.evidenceEntryDigest = Assurance.Digest ""
  , Assurance.evidenceObligationRevision = revision
  , Assurance.evidenceAssuranceKind = Assurance.KernelChecked
  , Assurance.evidenceRole = Assurance.EvidenceRole "establishes"
  , Assurance.evidenceProducer = "audit adapter of actual resolver result"
  , Assurance.evidenceChecker = "Phil Core"
  , Assurance.evidenceArtifact = Nothing
  , Assurance.evidenceInputDigests = []
  , Assurance.evidenceAssumptions = []
  , Assurance.evidenceDependsOn = []
  , Assurance.evidenceValidityScope = Assurance.ValidityScope Map.empty
  , Assurance.evidenceResult = Assurance.EvidenceAccepted
  , Assurance.evidenceJustifies =
      ["conditional local result; exact returned prerequisites retained separately"]
  , Assurance.evidenceRuntimeMechanism = Nothing
  , Assurance.evidenceRuntimeResidue = []
  , Assurance.evidenceCostRefs = []
  }

revisionOf :: Handoff.LedgerHandoff -> Assurance.RevisionId
revisionOf = Assurance.revisionId . Handoff.handoffRevision

parentEvidence :: Handoff.LedgerHandoff -> Either String Assurance.EvidenceEntry
parentEvidence entry = case Handoff.handoffDisposition entry of
  Discharge.StaticallyDischarged Discharge.StaticByDefinition ->
    Right (sealEvidence (baseEvidence (revisionOf entry)))
  other -> Left ("unexpected parent disposition: " <> show other)

runtimeEvidence :: Handoff.LedgerHandoff -> Either String Assurance.EvidenceEntry
runtimeEvidence entry = case Handoff.handoffDisposition entry of
  Discharge.RuntimeBound actual
    | actual == runtimeBinding -> Right . sealEvidence $
        (baseEvidence (revisionOf entry))
          { Assurance.evidenceEntryId = runtimeEvidenceId
          , Assurance.evidenceAssuranceKind = Assurance.RuntimeEnforced
          , Assurance.evidenceRole = Assurance.EvidenceRole "runtime"
          , Assurance.evidenceProducer = Discharge.runtimeValidator actual
          , Assurance.evidenceJustifies =
              [Assurance.renderPropositionCanonical (Discharge.runtimeProposition actual)]
          , Assurance.evidenceRuntimeMechanism = Just Assurance.RuntimeMechanism
              { Assurance.runtimeMechanismName = Discharge.runtimeValidator actual
              , Assurance.runtimeExecutionPoint = Discharge.runtimeRequiredPoint actual
              , Assurance.runtimeSuccessEvidenceType =
                  Text.pack (show (Discharge.runtimeSuccessEvidence actual))
              , Assurance.runtimeFailureContract =
                  Discharge.runtimeFailureClass actual <> ": "
                    <> Discharge.runtimeResourceContract actual
              , Assurance.runtimeImplementation = Nothing
              }
          , Assurance.evidenceRuntimeResidue = ["retain exact declared order check"]
          , Assurance.evidenceCostRefs = [Discharge.runtimeCostRef actual]
          }
  other -> Left ("unexpected prerequisite disposition: " <> show other)

mkExport :: Handoff.LedgerHandoff -> Assurance.ExportEntry
mkExport entry = sealed
  where
    raw = Assurance.ExportEntry
      { Assurance.exportId = childExportId
      , Assurance.exportDigest = Assurance.Digest ""
      , Assurance.exportObligationRevision = revisionOf entry
      , Assurance.exportBoundary = exportBoundary
      , Assurance.exportReplacementObligation =
          ObligationId "external:audit.final-operation-support.child"
      , Assurance.exportValidityScope = Assurance.ValidityScope Map.empty
      }
    sealed = raw { Assurance.exportDigest = Assurance.deriveExportDigest raw }

data Fixture = Fixture
  { fixtureEntries :: [Handoff.LedgerHandoff]
  , fixtureParent :: Handoff.LedgerHandoff
  , fixtureChild :: Handoff.LedgerHandoff
  , fixtureEvidence :: [Assurance.EvidenceEntry]
  , fixtureScope :: Set.Set Assurance.RevisionId
  , fixtureSelected :: Set.Set Assurance.EvidenceEntryId
  , fixtureExports :: [Assurance.ExportEntry]
  }

baseFixture :: Either String Fixture
baseFixture = do
  resolved <- resolveDefinition
  entries <- right $ Handoff.handoffResolvedObligation handoffConfig resolved
  (parent, child) <- case entries of
    [parentEntry, childEntry] -> Right (parentEntry, childEntry)
    other -> Left ("expected parent and prerequisite handoff, got " <> show other)
  parentEntry <- parentEvidence parent
  childEntry <- runtimeEvidence child
  let expectedSupport = Set.singleton (revisionOf parent, revisionOf child)
  ensure (Handoff.handoffSupportEdges entries == expectedSupport)
    "resolver prerequisite support was not retained in the handoff"
  Right Fixture
    { fixtureEntries = entries
    , fixtureParent = parent
    , fixtureChild = child
    , fixtureEvidence = [parentEntry, childEntry]
    , fixtureScope = Set.fromList [revisionOf parent, revisionOf child]
    , fixtureSelected = Set.fromList [parentEvidenceId, runtimeEvidenceId]
    , fixtureExports = []
    }

exportChild :: Fixture -> Fixture
exportChild fixture = fixture
  { fixtureScope = Set.singleton (revisionOf (fixtureParent fixture))
  , fixtureSelected = Set.singleton parentEvidenceId
  , fixtureExports = [mkExport (fixtureChild fixture)]
  }

closeFixture
  :: Fixture
  -> Either String (Either Closure.ManifestClosureError Assurance.AssuranceManifest)
closeFixture fixture = do
  graph <- right $ Verification.buildVerificationRevisionGraphWithSupport
    (map Handoff.handoffRevision (fixtureEntries fixture))
    (Handoff.handoffSupportEdges (fixtureEntries fixture))
    (fixtureScope fixture)
  let policy = Verification.ApplicationAssurancePolicy
        (Verification.AssurancePolicyRevision "audit.final-operation-support.policy")
        (Set.fromList
          [ Verification.StaticallyDischarged
          , Verification.RuntimeBound
          , Verification.Exported
          ])
  bundle <- right $ Bundle.buildVerificationBundle
    (Assurance.digestText "audit.final-operation-support.source")
    [] [] [] graph policy (fixtureEvidence fixture)
  let ledger = Assurance.emptyLedger
        { Assurance.ledgerRevisions = Verification.verificationGraphNodes graph
        , Assurance.ledgerEvidence = Map.fromList
            [ (Assurance.evidenceEntryId entry, entry)
            | entry <- fixtureEvidence fixture
            ]
        , Assurance.ledgerExports = Map.fromList
            [ (Assurance.exportId entry, entry)
            | entry <- fixtureExports fixture
            ]
        }
      context = Assurance.emptyVerificationContext
        { Assurance.verificationArchitectureDigest =
            Bundle.verificationBundleArchitectureDigest bundle
        , Assurance.verificationPhilCoreDigest =
            Assurance.digestText "audit.final-operation-support.core"
        , Assurance.verificationImplementationDigest =
            Assurance.digestText "audit.final-operation-support.implementation"
        , Assurance.verificationTarget = "audit-target"
        , Assurance.verificationCompilationProfile = "checked-runtime"
        , Assurance.verificationExpectedObligations =
            Map.keysSet (Verification.verificationGraphNodes graph)
        , Assurance.verificationLoweringLedgerRoot =
            Assurance.digestText "audit.final-operation-support.lowering"
        , Assurance.verificationKnownCostRefs = Set.singleton runtimeCost
        , Assurance.verificationPermittedExportBoundaries = Set.singleton exportBoundary
        }
      selection = Closure.ManifestClosureSelection
        { Closure.manifestClosureEvidence = fixtureSelected fixture
        , Closure.manifestClosureAssumptions = Set.empty
        , Closure.manifestClosureExports = Map.fromList
            [ (Assurance.exportId entry, Verification.Exported)
            | entry <- fixtureExports fixture
            ]
        , Closure.manifestClosureUses = Set.empty
        }
      handoff = Closure.ManifestClosureHandoff
        { Closure.manifestClosureHandoffEntries = fixtureEntries fixture
        , Closure.manifestClosureCertificateEvidence = Map.empty
        , Closure.manifestClosureDirectEvidence = Map.empty
        }
  Right $ Closure.closeVerificationBundleWithHandoff
    bundle policy context ledger selection handoff

fullScopeDefinitionAccepted :: Either String ()
fullScopeDefinitionAccepted = do
  fixture <- baseFixture
  result <- closeFixture fixture
  manifest <- right result
  ensure
    (Assurance.manifestCertificationScope manifest == fixtureScope fixture)
    "full-scope closure changed the certification scope"
  ensure
    (Assurance.manifestEvidenceEntries manifest == fixtureSelected fixture)
    "full-scope closure changed selected evidence"

exportedDefinitionSupportRejected :: Either String ()
exportedDefinitionSupportRejected = do
  fixture <- baseFixture
  let changed = exportChild fixture
      parentRevision = revisionOf (fixtureParent fixture)
      childRevision = revisionOf (fixtureChild fixture)
  result <- closeFixture changed
  case result of
    Left (Closure.ManifestClosureHandoffRequiredSupportOutOfScope actualParent actualChild)
      | actualParent == parentRevision
      , actualChild == childRevision -> Right ()
    other -> Left
      ("expected exact retained-support scope rejection, got " <> show other)
