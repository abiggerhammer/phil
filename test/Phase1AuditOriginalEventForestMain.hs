{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (KernelChecked, RuntimeEnforced)
  , EvidenceRole (..)
  , HandoffConfig (..)
  , LedgerHandoff (..)
  , OriginalCheckEventAcceptance (..)
  , OriginalCheckEventClosureError (..)
  , OriginalCheckEventError (..)
  , actualEvidenceSubjectEndpoints
  , actualEvidenceUseInventory
  , closeOriginalCheckEventBundle
  , closeOriginalCheckEventBundleWithAuthority
  , handoffOriginalCheckEvent
  , handoffSupportEdges
  , resolveOriginalCheckEvent
  , revisionId
  )
import qualified Phil.Assurance as Assurance
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import qualified Phil.Core.Discharge as Discharge
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValueWithResidual)
import qualified Phil.Verification as Verification
import qualified Phil.Verification.Bundle as Bundle
import qualified Phil.Verification.ManifestClosure as Closure
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ run "C01" "definitionally closed parent retains runtime prerequisite" definitionParentRetainsPrerequisite
    , run "C02" "actual residual root and child retain one original event forest" residualRootRetainsForest
    , run "C03" "wrong residual occurrence id cannot rebase the checked result" wrongOccurrenceRejected
    , run "C04" "wrong scope metadata cannot rebase the checked result" wrongScopeRejected
    , run "C05" "dropped returned residual use cannot shrink the event inventory" droppedResidualUseRejected
    , run "C06" "fully static literal subtraction remains valid" staticLiteralRemainsValid
    , run "C07" "final manifest closure consumes the event-derived handoff" finalClosureUsesActualEvent
    , run "C08" "final manifest closure rejects a graph that drops event support" finalClosureRejectsShrunkSupport
    , run "C09" "successful closure reflects the exact accepting operation inputs" finalClosureReflectsAcceptingOperation
    ]
  unless (and results) exitFailure
  putStrLn "COMPLETE original_check_event_forest_controls=8"

run :: String -> String -> Either String () -> IO Bool
run ident label result =
  case result of
    Right () -> putStrLn ("PASS " <> ident <> " " <> label) >> pure True
    Left detail -> putStrLn ("FAIL " <> ident <> " " <> detail) >> pure False

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False detail = Left detail

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

n :: Text -> Name
n = Name

v :: Text -> RefTerm
v = RefVar . n

natTy :: Ty
natTy = TyOpaqueSorted "AuditNat" SortNat

natState :: Either String CheckState
natState = foldM add emptyCheckState ["a", "b"]
  where
    add state name = do
      context <- right $ insertBinding Unrestricted (n name) natTy (resourceContext state)
      Right state { resourceContext = context }

side :: Proposition
side = LessEqual (v "b") (v "a")

reflexiveDifference :: Proposition
reflexiveDifference =
  Equal
    (RefSub (v "a") (v "b"))
    (RefSub (v "a") (v "b"))

usedGoal :: Proposition
usedGoal = Conjunction reflexiveDifference side

rootId, childId :: ObligationId
rootId = ObligationId "audit.original-event.root"
childId = ObligationId "audit.original-event.root.nat-sub.1"

spec :: ResidualSpec
spec = ResidualSpec
  { residualObligationId = rootId
  , residualOrigin = "Phase1AuditOriginalEventForest"
  , residualScope = "audit.original-event.scope"
  , residualRequiredPoint = "before-consumer"
  }

childObligation :: Obligation
childObligation = Obligation
  { obligationId = childId
  , obligationProposition = side
  , obligationOrigin = residualOrigin spec
  , obligationScope = residualScope spec
  , obligationRequiredPoint = residualRequiredPoint spec
  }

runtimeFor :: Obligation -> Discharge.RuntimeBinding
runtimeFor obligation = Discharge.RuntimeBinding
  { Discharge.runtimeObligationId = obligationId obligation
  , Discharge.runtimeProposition = obligationProposition obligation
  , Discharge.runtimeRequiredPoint = obligationRequiredPoint obligation
  , Discharge.runtimeValidator = "audit-runtime-check"
  , Discharge.runtimeSuccessEvidence = TyProof (obligationProposition obligation)
  , Discharge.runtimeFailureClass = "ValidationFailure"
  , Discharge.runtimeResourceContract = "preserve unrelated resources"
  , Discharge.runtimeCostRef = runtimeCost
  }

runtimeCost :: Text
runtimeCost = "audit.original-event.runtime"

runtimeChildPolicy :: Either String Discharge.DischargePolicy
runtimeChildPolicy = right $
  Discharge.bindRuntime (runtimeFor childObligation) Discharge.emptyDischargePolicy

emit :: Proposition -> Either String ValueResult
emit proposition = do
  state <- natState
  right $
    checkValueWithResidual
      spec
      (VBool True)
      (TyRefined (n "value") TyBool proposition)
      state

config :: HandoffConfig
config = HandoffConfig
  { handoffRevisionKind = const "Audit"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const ["audit.original-event.subject"]
  , handoffContextIds = const ["audit.original-event.context"]
  , handoffAcceptanceRule = \obligation ->
      if obligationId obligation == childId
        then AcceptEntry RuntimeEnforced (EvidenceRole "runtime")
        else AcceptEntry KernelChecked (EvidenceRole "establishes")
  }

definitionParentRetainsPrerequisite :: Either String ()
definitionParentRetainsPrerequisite = do
  result <- emit reflexiveDifference
  let pending = residualObligations (valueResultState result)
  ensure
    (pending == Map.singleton childId childObligation)
    ("unexpected emitted residual map: " <> show pending)
  policy <- runtimeChildPolicy
  resolved <- right $
    resolveOriginalCheckEvent emptyStaticContext policy spec result
  ensure
    (obligationProposition (Discharge.resolvedObligation resolved) == reflexiveDifference)
    "original unnormalized goal was not retained as the forest root"
  case Discharge.resolvedDisposition resolved of
    Discharge.StaticallyDischarged Discharge.StaticByDefinition -> Right ()
    other -> Left ("expected definitionally discharged parent, got " <> show other)
  child <- onlyChild resolved
  case Discharge.resolvedDisposition child of
    Discharge.RuntimeBound binding ->
      ensure
        (Discharge.runtimeObligationId binding == childId)
        "runtime prerequisite changed identity"
    other -> Left ("expected runtime-bound prerequisite, got " <> show other)
  entries <- right $
    handoffOriginalCheckEvent config Map.empty emptyStaticContext policy spec result
  assertParentChildSupport entries

residualRootRetainsForest :: Either String ()
residualRootRetainsForest = do
  result <- emit usedGoal
  let pendingIds = Map.keysSet (residualObligations (valueResultState result))
  ensure
    (pendingIds == Set.fromList [rootId, childId])
    ("unexpected residual root/child inventory: " <> show pendingIds)
  policy <- runtimeChildPolicy
  resolved <- right $
    resolveOriginalCheckEvent emptyStaticContext policy spec result
  case Discharge.resolvedDisposition resolved of
    Discharge.StaticallyDischarged Discharge.StaticByCertificate {} -> Right ()
    other -> Left ("expected prerequisite-backed parent certificate, got " <> show other)
  _ <- onlyChild resolved
  entries <- right $
    handoffOriginalCheckEvent config Map.empty emptyStaticContext policy spec result
  assertParentChildSupport entries

wrongOccurrenceRejected :: Either String ()
wrongOccurrenceRejected = do
  result <- emit reflexiveDifference
  let wrong = spec { residualObligationId = ObligationId "audit.other.root" }
      wrongChild =
        childObligation
          { obligationId = ObligationId "audit.other.root.nat-sub.1"
          }
  policy <- right $
    Discharge.bindRuntime (runtimeFor wrongChild) Discharge.emptyDischargePolicy
  case resolveOriginalCheckEvent emptyStaticContext policy wrong result of
    Left (OriginalCheckEventResidualCoverageMismatch _ _) -> Right ()
    Left (OriginalCheckEventResidualInventoryMismatch _ _) -> Right ()
    other -> Left ("wrong occurrence was not rejected by exact coverage: " <> show other)

wrongScopeRejected :: Either String ()
wrongScopeRejected = do
  result <- emit reflexiveDifference
  policy <- runtimeChildPolicy
  let wrong = spec { residualScope = "audit.other.scope" }
  case resolveOriginalCheckEvent emptyStaticContext policy wrong result of
    Left (OriginalCheckEventResidualMetadataMismatch _ _ _) -> Right ()
    other -> Left ("wrong scope was not rejected by emitted metadata: " <> show other)

droppedResidualUseRejected :: Either String ()
droppedResidualUseRejected = do
  result <- emit reflexiveDifference
  policy <- runtimeChildPolicy
  let tampered = result
        { valueResultEvidence =
            [ use
            | use <- valueResultEvidence result
            , case use of
                EvidenceResidual _ _ -> False
                _ -> True
            ]
        }
  case resolveOriginalCheckEvent emptyStaticContext policy spec tampered of
    Left (OriginalCheckEventResidualInventoryMismatch _ _) -> Right ()
    other -> Left ("dropped residual use did not fail closed: " <> show other)

staticLiteralRemainsValid :: Either String ()
staticLiteralRemainsValid = do
  state <- natState
  let literalDifference =
        Equal
          (RefSub (RefNat 5) (RefNat 3))
          (RefSub (RefNat 5) (RefNat 3))
  result <- right $
    checkValueWithResidual
      spec
      (VBool True)
      (TyRefined (n "value") TyBool literalDifference)
      state
  ensure
    (Map.null (residualObligations (valueResultState result)))
    "valid literal equality unexpectedly became residual"
  resolved <- right $
    resolveOriginalCheckEvent
      emptyStaticContext
      Discharge.emptyDischargePolicy
      spec
      result
  case Discharge.resolvedDisposition resolved of
    Discharge.StaticallyDischarged Discharge.StaticByDefinition -> Right ()
    other -> Left ("valid literal equality stopped being definitionally valid: " <> show other)

finalClosureUsesActualEvent :: Either String ()
finalClosureUsesActualEvent = do
  (result, entries, _, _, closureResult) <- closeActualEvent True
  ensure
    (EvidenceResidual childId side `elem` valueResultEvidence result)
    "actual checker result did not retain its residual prerequisite use"
  manifest <- right closureResult
  let expectedScope = Set.fromList (map (revisionId . handoffRevision) entries)
  ensure
    (Assurance.manifestCertificationScope manifest == expectedScope)
    "final closure changed the exact event-derived certification scope"

finalClosureRejectsShrunkSupport :: Either String ()
finalClosureRejectsShrunkSupport = do
  (_, entries, _, _, closureResult) <- closeActualEvent False
  let expected = handoffSupportEdges entries
  ensure (not (Set.null expected)) "fixture unexpectedly has no event support edge"
  case closureResult of
    Left (OriginalCheckEventClosureManifestError
        (Closure.ManifestClosureHandoffSupportMismatch actualExpected actualGraph))
      | actualExpected == expected
      , Set.null actualGraph -> Right ()
    other -> Left
      ("expected exact event support mismatch at final closure, got " <> show other)

finalClosureReflectsAcceptingOperation :: Either String ()
finalClosureReflectsAcceptingOperation = do
  (result, entries, selection, authorityResult, legacyResult) <- closeActualEvent True
  accepted <- right authorityResult
  legacyManifest <- right legacyResult
  expectedEndpoints <- right $ actualEvidenceSubjectEndpoints spec result
  ensure
    (originalCheckEventAcceptedSpec accepted == spec)
    "successful closure did not retain the exact producer spec"
  ensure
    (originalCheckEventAcceptedEvidenceUses accepted == actualEvidenceUseInventory result)
    "successful closure did not retain the authentic ordered evidence-use inventory"
  ensure
    (originalCheckEventAcceptedSubjectEndpoints accepted == expectedEndpoints)
    "successful closure did not retain the exact same-event occurrence endpoints"
  ensure
    (originalCheckEventAcceptedHandoff accepted == entries)
    "successful closure did not retain the exact event-derived handoff"
  ensure
    (originalCheckEventAcceptedSelection accepted == selection)
    "successful closure did not retain the exact final selection"
  ensure
    (originalCheckEventAcceptedManifest accepted == legacyManifest)
    "legacy manifest projection diverged from authoritative closure"
  ensure
    (Assurance.manifestAssuranceUses legacyManifest == Closure.manifestClosureUses selection)
    "returned manifest did not retain the accepting operation's exact assurance-use selection"

closeActualEvent
  :: Bool
  -> Either String
      ( ValueResult
      , [LedgerHandoff]
      , Closure.ManifestClosureSelection
      , Either OriginalCheckEventClosureError OriginalCheckEventAcceptance
      , Either OriginalCheckEventClosureError Assurance.AssuranceManifest
      )
closeActualEvent keepSupport = do
  result <- emit reflexiveDifference
  dischargePolicy <- runtimeChildPolicy
  entries <- right $
    handoffOriginalCheckEvent
      config Map.empty emptyStaticContext dischargePolicy spec result
  (parent, child) <- case entries of
    [parentEntry, childEntry] -> Right (parentEntry, childEntry)
    other -> Left ("expected parent and child handoff entries, got " <> show other)
  parentEntry <- definitionEvidence parent
  childEntry <- runtimeEvidence child
  let fullSupport = handoffSupportEdges entries
      selectedSupport = if keepSupport then fullSupport else Set.empty
      scope = Set.fromList [revisionId (handoffRevision parent), revisionId (handoffRevision child)]
      evidence = [parentEntry, childEntry]
      assurancePolicy = Verification.ApplicationAssurancePolicy
        (Verification.AssurancePolicyRevision "audit.original-event.final.policy")
        (Set.fromList [Verification.StaticallyDischarged, Verification.RuntimeBound])
  graph <- right $
    Verification.buildVerificationRevisionGraphWithSupport
      (map handoffRevision entries)
      selectedSupport
      scope
  bundle <- right $
    Bundle.buildVerificationBundle
      (Assurance.digestText "audit.original-event.final.source")
      [] [] [] graph assurancePolicy evidence
  let ledger = Assurance.emptyLedger
        { Assurance.ledgerRevisions = Verification.verificationGraphNodes graph
        , Assurance.ledgerEvidence = Map.fromList
            [ (Assurance.evidenceEntryId entry, entry)
            | entry <- evidence
            ]
        }
      context = Assurance.emptyVerificationContext
        { Assurance.verificationArchitectureDigest =
            Bundle.verificationBundleArchitectureDigest bundle
        , Assurance.verificationPhilCoreDigest =
            Assurance.digestText "audit.original-event.final.core"
        , Assurance.verificationImplementationDigest =
            Assurance.digestText "audit.original-event.final.implementation"
        , Assurance.verificationTarget = "audit-target"
        , Assurance.verificationCompilationProfile = "checked-runtime"
        , Assurance.verificationExpectedObligations =
            Map.keysSet (Verification.verificationGraphNodes graph)
        , Assurance.verificationLoweringLedgerRoot =
            Assurance.digestText "audit.original-event.final.lowering"
        , Assurance.verificationKnownCostRefs = Set.singleton runtimeCost
        }
      selection = Closure.ManifestClosureSelection
        { Closure.manifestClosureEvidence =
            Set.fromList [parentEvidenceId, runtimeEvidenceId]
        , Closure.manifestClosureAssumptions = Set.empty
        , Closure.manifestClosureExports = Map.empty
        , Closure.manifestClosureUses = Set.empty
        }
      authorityResult = closeOriginalCheckEventBundleWithAuthority
        config
        emptyStaticContext
        dischargePolicy
        spec
        result
        bundle
        assurancePolicy
        context
        ledger
        selection
        Map.empty
        Map.empty
      closureResult = closeOriginalCheckEventBundle
        config
        emptyStaticContext
        dischargePolicy
        spec
        result
        bundle
        assurancePolicy
        context
        ledger
        selection
        Map.empty
        Map.empty
  Right (result, entries, selection, authorityResult, closureResult)

parentEvidenceId, runtimeEvidenceId :: Assurance.EvidenceEntryId
parentEvidenceId = Assurance.EvidenceEntryId "audit.original-event.final.parent"
runtimeEvidenceId = Assurance.EvidenceEntryId "audit.original-event.final.runtime"

sealEvidence :: Assurance.EvidenceEntry -> Assurance.EvidenceEntry
sealEvidence entry = entry
  { Assurance.evidenceEntryDigest = Assurance.deriveEvidenceEntryDigest entry }

baseEvidence
  :: Assurance.EvidenceEntryId
  -> Assurance.AssuranceKind
  -> Assurance.EvidenceRole
  -> LedgerHandoff
  -> Assurance.EvidenceEntry
baseEvidence entryId kind role entry = Assurance.EvidenceEntry
  { Assurance.evidenceEntryId = entryId
  , Assurance.evidenceEntryDigest = Assurance.Digest ""
  , Assurance.evidenceObligationRevision = revisionId (handoffRevision entry)
  , Assurance.evidenceAssuranceKind = kind
  , Assurance.evidenceRole = role
  , Assurance.evidenceProducer = "actual original-event final closure regression"
  , Assurance.evidenceChecker = "Phil Core"
  , Assurance.evidenceArtifact = Nothing
  , Assurance.evidenceInputDigests = []
  , Assurance.evidenceAssumptions = []
  , Assurance.evidenceDependsOn = []
  , Assurance.evidenceValidityScope = Assurance.ValidityScope Map.empty
  , Assurance.evidenceResult = Assurance.EvidenceAccepted
  , Assurance.evidenceJustifies = ["exact event-derived disposition"]
  , Assurance.evidenceRuntimeMechanism = Nothing
  , Assurance.evidenceRuntimeResidue = []
  , Assurance.evidenceCostRefs = []
  }

definitionEvidence :: LedgerHandoff -> Either String Assurance.EvidenceEntry
definitionEvidence entry =
  case handoffDisposition entry of
    Discharge.StaticallyDischarged Discharge.StaticByDefinition ->
      Right . sealEvidence $
        baseEvidence
          parentEvidenceId
          KernelChecked
          (EvidenceRole "establishes")
          entry
    other -> Left ("unexpected final parent disposition: " <> show other)

runtimeEvidence :: LedgerHandoff -> Either String Assurance.EvidenceEntry
runtimeEvidence entry =
  case handoffDisposition entry of
    Discharge.RuntimeBound binding ->
      Right . sealEvidence $
        (baseEvidence runtimeEvidenceId RuntimeEnforced (EvidenceRole "runtime") entry)
          { Assurance.evidenceProducer = Discharge.runtimeValidator binding
          , Assurance.evidenceJustifies =
              [Assurance.renderPropositionCanonical (Discharge.runtimeProposition binding)]
          , Assurance.evidenceRuntimeMechanism = Just Assurance.RuntimeMechanism
              { Assurance.runtimeMechanismName = Discharge.runtimeValidator binding
              , Assurance.runtimeExecutionPoint = Discharge.runtimeRequiredPoint binding
              , Assurance.runtimeSuccessEvidenceType =
                  Text.pack (show (Discharge.runtimeSuccessEvidence binding))
              , Assurance.runtimeFailureContract =
                  Discharge.runtimeFailureClass binding <> ": "
                    <> Discharge.runtimeResourceContract binding
              , Assurance.runtimeImplementation = Nothing
              }
          , Assurance.evidenceRuntimeResidue = ["retain exact declared order check"]
          , Assurance.evidenceCostRefs = [Discharge.runtimeCostRef binding]
          }
    other -> Left ("unexpected final prerequisite disposition: " <> show other)

onlyChild :: Discharge.ResolvedObligation -> Either String Discharge.ResolvedObligation
onlyChild resolved =
  case Discharge.resolvedPrerequisites resolved of
    [child] -> Right child
    children -> Left ("expected one original prerequisite, got " <> show children)

assertParentChildSupport :: [LedgerHandoff] -> Either String ()
assertParentChildSupport entries =
  case entries of
    [parent, child] -> do
      let edge =
            ( revisionId (handoffRevision parent)
            , revisionId (handoffRevision child)
            )
      ensure
        (handoffSupportEdges entries == Set.singleton edge)
        ("original event support edge was not retained: " <> show (handoffSupportEdges entries))
    other -> Left ("expected parent and child handoff nodes, got " <> show other)