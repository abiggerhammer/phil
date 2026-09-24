{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Assurance (resolveOriginalCheckEvent)
import Phil.Core.Checker
  ( CheckState (..)
  , LogicalSubjectSupport (..)
  , emptyCheckState
  )
import Phil.Core.Context (ResourceContext (..), insertBinding)
import qualified Phil.Core.Discharge as Discharge
import Phil.Core.Refinement (ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual)
import System.Exit (exitFailure)

payload, binder :: Name
payload = Name "payload"
binder = Name "subject"

boundTy, targetTy :: Ty
boundTy = TyRefined binder (TyUInt 8)
  (LessEqual (RefToNat (RefVar binder)) (RefNat 1))
targetTy = TyRefined binder (TyUInt 8)
  (LessThan (RefToNat (RefVar binder)) (RefNat 5))

target :: Proposition
target = LessThan (RefToNat (RefVar payload)) (RefNat 5)

spec :: ResidualSpec
spec = ResidualSpec
  { residualObligationId = ObligationId "audit.refined-consumed-event"
  , residualOrigin = "Phase1AuditRefinedConsumedEvent"
  , residualScope = "audit.refined-consumed.scope"
  , residualRequiredPoint = "before-consumer"
  }

root :: Obligation
root = Obligation
  { obligationId = residualObligationId spec
  , obligationProposition = target
  , obligationOrigin = residualOrigin spec
  , obligationScope = residualScope spec
  , obligationRequiredPoint = residualRequiredPoint spec
  }

runtimeFor :: Obligation -> Discharge.RuntimeBinding
runtimeFor obligation = Discharge.RuntimeBinding
  { Discharge.runtimeObligationId = obligationId obligation
  , Discharge.runtimeProposition = obligationProposition obligation
  , Discharge.runtimeRequiredPoint = obligationRequiredPoint obligation
  , Discharge.runtimeValidator = "audit-refined-consumed-validator"
  , Discharge.runtimeSuccessEvidence = TyProof (obligationProposition obligation)
  , Discharge.runtimeFailureClass = "ValidationFailure"
  , Discharge.runtimeResourceContract = "do not restore consumed owner"
  , Discharge.runtimeCostRef = "audit.refined-consumed.cost"
  }

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False detail = Left detail

fixture :: Mode -> Either String (CheckState, ValueResult)
fixture mode = do
  literal <- right $ checkValue (VUInt 8 0) boundTy emptyCheckState
  context <- right $
    insertBinding mode payload (valueResultType literal) (resourceContext emptyCheckState)
  let before = emptyCheckState { resourceContext = context }
  result <- right $ checkValueWithResidual spec (VVar payload) targetTy before
  ensure (valueResultTerm result == Just (RefVar payload)) "checked subject changed"
  ensure (valueResultType result == targetTy) "checked target type changed"
  ensure (valueResultMode result == Just mode) "checked structural mode changed"
  Right (before, result)

prepared
  :: Mode
  -> Either String (ValueResult, Obligation, Discharge.DischargePolicy)
prepared mode = do
  (before, result) <- fixture mode
  let after = valueResultState result
      context = resourceContext after
  ensure (resourceContext before /= context) "restricted value was not consumed"
  ensure
    ( Map.notMember payload (unrestrictedBindings context)
      && Map.notMember payload (affineBindings context)
      && Map.notMember payload (linearBindings context)
    )
    "consumed owner remains available"
  obligation <- maybe (Left "actual residual missing") Right $
    Map.lookup (obligationId root) (residualObligations after)
  ensure (obligation == root) "actual original requirement changed"
  support <- maybe (Left "captured logical subject missing") Right $
    Map.lookup (obligationId root) (residualLogicalSubjects after)
  ensure (logicalSupportObligation support == root) "support names a different event"
  ensure
    (Map.lookup payload (logicalSupportBindings support) == Just boundTy)
    "exact retained refined interpretation was lost"
  ensure
    (Map.notMember payload (logicalSupportUnrestrictedBindings support))
    "restricted retained subject gained unrestricted authority"
  policy <- right $
    Discharge.bindRuntime (runtimeFor root) Discharge.emptyDischargePolicy
  Right (result, obligation, policy)

ordinary
  :: Mode
  -> Either String (ValueResult, Discharge.DischargePolicy, Discharge.ResolvedObligation)
ordinary mode = do
  (result, obligation, policy) <- prepared mode
  resolved <- right $
    Discharge.resolveObligation emptyStaticContext (valueResultState result) policy obligation
  ensure (Discharge.resolvedObligation resolved == obligation) "ordinary resolver changed event"
  ensure
    (Discharge.resolvedDisposition resolved == Discharge.RuntimeBound (runtimeFor obligation))
    "ordinary resolver changed declared runtime responsibility"
  ensure (null (Discharge.resolvedPrerequisites resolved)) "ordinary resolver invented a child"
  Right (result, policy, resolved)

adapter :: Mode -> Either String ()
adapter mode = do
  (result, policy, expected) <- ordinary mode
  actual <- right $ resolveOriginalCheckEvent emptyStaticContext policy spec result
  ensure (actual == expected) "event adapter changed retained interpretation or identity"
  let context = resourceContext (valueResultState result)
  ensure
    ( Map.notMember payload (unrestrictedBindings context)
      && Map.notMember payload (affineBindings context)
      && Map.notMember payload (linearBindings context)
    )
    "event adapter restored the consumed owner"

main :: IO ()
main = do
  results <- sequence
    [ run "C01" "linear actual check consumes owner and retains exact refined support" (prepared Linear >> pure ())
    , run "C02" "linear ordinary resolver interprets exact residual under runtime policy" (ordinary Linear >> pure ())
    , run "C03" "affine actual check consumes owner and retains exact refined support" (prepared Affine >> pure ())
    , run "C04" "affine ordinary resolver interprets exact residual under runtime policy" (ordinary Affine >> pure ())
    , run "R01" "linear original-event adapter uses retained logical interpretation without ownership" (adapter Linear)
    , run "R02" "affine original-event adapter uses retained logical interpretation without ownership" (adapter Affine)
    ]
  unless (and results) exitFailure
  putStrLn "COMPLETE refined_consumed_event_controls=6"

run :: String -> String -> Either String () -> IO Bool
run ident label result =
  case result of
    Right () -> putStrLn ("PASS " <> ident <> " " <> label) >> pure True
    Left detail -> putStrLn ("FAIL " <> ident <> " " <> label <> " -- " <> detail) >> pure False
