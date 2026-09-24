{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (KernelChecked)
  , EvidenceRole (..)
  , HandoffConfig (..)
  , LedgerHandoff (..)
  , OriginalCheckEventError (..)
  , handoffOriginalCheckEvent
  , handoffSupportEdges
  , resolveOriginalCheckEvent
  , revisionId
  )
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import qualified Phil.Core.Discharge as Discharge
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValueWithResidual)
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
    ]
  unless (and results) exitFailure
  putStrLn "COMPLETE original_check_event_forest_controls=6"

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
  , Discharge.runtimeCostRef = "audit.original-event.runtime"
  }

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
  , handoffAcceptanceRule = const (AcceptEntry KernelChecked (EvidenceRole "audit"))
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
