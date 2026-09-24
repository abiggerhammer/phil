{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Phil.Assurance as Assurance
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import qualified Phil.Core.Discharge as D
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
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

bound, target :: Proposition
bound = LessEqual (RefToNat (RefVar payload)) (RefNat 1)
target = LessThan (RefToNat (RefVar payload)) (RefNat 5)

spec :: ResidualSpec
spec = ResidualSpec
  { residualObligationId = ObligationId "audit.event-adapter.refined"
  , residualOrigin = "audit-event-adapter-preservation"
  , residualScope = "audit.same-original"
  , residualRequiredPoint = "before consumer"
  }

rootFor :: Proposition -> Obligation
rootFor proposition = Obligation
  { obligationId = residualObligationId spec
  , obligationProposition = proposition
  , obligationOrigin = residualOrigin spec
  , obligationScope = residualScope spec
  , obligationRequiredPoint = residualRequiredPoint spec
  }

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

checkedLiteral :: Either String ValueResult
checkedLiteral = do
  literal <- right $ checkValue (VUInt 8 0) boundTy emptyCheckState
  assert (valueResultType literal == boundTy) "wrong checked refined type"
  assert (valueResultTerm literal == Just (RefUInt 8 0)) "wrong checked literal"
  Right literal

fixture :: Ty -> Ty -> Mode -> Either String (CheckState, ValueResult)
fixture initialTy expected mode = do
  literal <- right $ checkValue (VUInt 8 0) initialTy emptyCheckState
  context <- right $ insertBinding mode payload (valueResultType literal)
    (resourceContext emptyCheckState)
  let before = emptyCheckState { resourceContext = context }
  result <- right $ checkValueWithResidual spec (VVar payload) expected before
  assert (valueResultTerm result == Just (RefVar payload)) "changed checked subject"
  assert (valueResultType result == expected) "changed expected type"
  assert (valueResultMode result == Just mode) "changed structural mode"
  Right (before,result)

liveResidual :: Either String (CheckState, ValueResult, Obligation)
liveResidual = do
  (before,result) <- fixture boundTy targetTy Unrestricted
  let after = valueResultState result
  assert (resourceContext before == resourceContext after) "resource state changed"
  obligation <- maybe (Left "missing actual residual") Right $
    Map.lookup (residualObligationId spec) (residualObligations after)
  assert (obligation == rootFor target) "wrong original residual"
  assert (EvidenceResidual (obligationId obligation) target `elem` valueResultEvidence result)
    "actual residual use missing"
  Right (before,result,obligation)

staticResult :: Proposition -> D.ResolvedObligation -> Either String ()
staticResult proposition resolved = do
  assert (D.resolvedObligation resolved == rootFor proposition) "changed original event"
  assert (D.resolvedCanonicalProposition resolved == proposition) "changed canonical goal"
  assert (null (D.resolvedPrerequisites resolved)) "invented prerequisites"
  case D.resolvedDisposition resolved of
    D.StaticallyDischarged _ -> Right ()
    other -> Left ("expected static result, got " <> show other)

ordinaryResidualResolver :: Either String ()
ordinaryResidualResolver = do
  (_,result,obligation) <- liveResidual
  resolved <- right $ D.resolveObligation emptyStaticContext
    (valueResultState result) D.emptyDischargePolicy obligation
  staticResult target resolved

carriedFixture :: Either String (CheckState, ValueResult)
carriedFixture = do
  (before,result) <- fixture boundTy boundTy Unrestricted
  assert (resourceContext before == resourceContext (valueResultState result))
    "unchanged original was consumed or replaced"
  assert (Map.null (residualObligations (valueResultState result)))
    "the actual checker did not finish the carried requirement"
  assert (EvidenceByBinding payload bound `elem` valueResultEvidence result)
    "actual successful evidence-use record missing"
  pure (before,result)

ordinaryCarriedResolver :: Either String ()
ordinaryCarriedResolver = do
  (_,result) <- carriedFixture
  resolved <- right $ D.resolveObligation emptyStaticContext
    (valueResultState result) D.emptyDischargePolicy (rootFor bound)
  staticResult bound resolved

runtimeFor :: Obligation -> D.RuntimeBinding
runtimeFor obligation = D.RuntimeBinding
  { D.runtimeObligationId = obligationId obligation
  , D.runtimeProposition = obligationProposition obligation
  , D.runtimeRequiredPoint = obligationRequiredPoint obligation
  , D.runtimeValidator = "declared-audit-validator"
  , D.runtimeSuccessEvidence = TyProof (obligationProposition obligation)
  , D.runtimeFailureClass = "ValidationFailure"
  , D.runtimeResourceContract = "no owner resurrection"
  , D.runtimeCostRef = "audit.event.runtime.cost"
  }

plainRuntime :: Mode -> Either String ()
plainRuntime mode = do
  (before,result) <- fixture (TyUInt 8) targetTy mode
  let after = valueResultState result
      obligation = rootFor target
  if mode == Unrestricted
    then assert (resourceContext before == resourceContext after) "unrestricted changed"
    else assert (Map.notMember payload (linearBindings (resourceContext after)))
      "linear owner was restored"
  assert (Map.lookup (obligationId obligation) (residualObligations after) == Just obligation)
    "wrong plain residual"
  policy <- right $ D.bindRuntime (runtimeFor obligation) D.emptyDischargePolicy
  resolved <- right $ Assurance.resolveOriginalCheckEvent emptyStaticContext policy spec result
  assert (D.resolvedObligation resolved == obligation) "event identity changed"
  assert (D.resolvedDisposition resolved == D.RuntimeBound (runtimeFor obligation))
    "declared runtime disposition changed"
  assert (null (D.resolvedPrerequisites resolved)) "unexpected child"

closedLiteral :: Either String ()
closedLiteral = do
  result <- right $ checkValueWithResidual spec (VUInt 8 0) targetTy emptyCheckState
  assert (Map.null (residualObligations (valueResultState result))) "literal became residual"
  resolved <- right $ Assurance.resolveOriginalCheckEvent
    emptyStaticContext D.emptyDischargePolicy spec result
  case D.resolvedDisposition resolved of
    D.StaticallyDischarged D.StaticByDefinition -> Right ()
    other -> Left ("closed literal changed: " <> show other)

noUnsupportedSuccess :: Either String ()
noUnsupportedSuccess = do
  (_,result) <- fixture (TyUInt 8) targetTy Unrestricted
  case Assurance.resolveOriginalCheckEvent emptyStaticContext D.emptyDischargePolicy spec result of
    Left (Assurance.OriginalCheckEventDischargeError (D.UnresolvedObligation _ _)) -> Right ()
    other -> Left ("unsupported plain value did not remain unresolved: " <> show other)

liveEventAdapter :: Either String ()
liveEventAdapter = do
  (_,result,_) <- liveResidual
  resolved <- right $ Assurance.resolveOriginalCheckEvent
    emptyStaticContext D.emptyDischargePolicy spec result
  staticResult target resolved

carriedEventAdapter :: Either String ()
carriedEventAdapter = do
  (_,result) <- carriedFixture
  resolved <- right $ Assurance.resolveOriginalCheckEvent
    emptyStaticContext D.emptyDischargePolicy spec result
  staticResult bound resolved

main :: IO ()
main = do
  rows <- sequence
    [ test "C01" "genuinely checked refined zero" (checkedLiteral >> pure ())
    , test "C02" "exact residual and unchanged original context" (liveResidual >> pure ())
    , test "C03" "ordinary resolver proves exact live-original residual" ordinaryResidualResolver
    , test "C04" "actual carried evidence and ordinary resolver remain valid" ordinaryCarriedResolver
    , test "C05" "plain unrestricted runtime event remains valid" (plainRuntime Unrestricted)
    , test "C06" "linear runtime event does not restore the owner" (plainRuntime Linear)
    , test "C07" "closed literal event remains valid" closedLiteral
    , test "C08" "unsupported plain event remains unresolved" noUnsupportedSuccess
    , test "R01" "original-event adapter preserves live refined residual" liveEventAdapter
    , test "R02" "original-event adapter preserves actual carried evidence" carriedEventAdapter
    ]
  putStrLn "COMPLETE correctness_groups=10"
  unless (and rows) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label outcome = case outcome of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left err -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> err) >> pure False
