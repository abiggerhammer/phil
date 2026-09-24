{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker
  ( CheckState (..)
  , LogicalSubjectSupport (..)
  , emptyCheckState
  )
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Discharge
  ( ObligationDisposition (..)
  , ResolvedObligation (..)
  , StaticDischarge (..)
  , emptyDischargePolicy
  , resolveObligation
  )
import Phil.Core.Refinement (ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual)
import System.Exit (exitFailure)

payload, binder, proofName :: Name
payload = Name "payload"
binder = Name "subject"
proofName = Name "originalProof"

boundTy, targetTy :: Ty
boundTy = TyRefined binder (TyUInt 8)
  (LessEqual (RefToNat (RefVar binder)) (RefNat 1))
targetTy = TyRefined binder (TyUInt 8)
  (LessThan (RefToNat (RefVar binder)) (RefNat 5))

required :: Proposition
required = LessThan (RefToNat (RefVar payload)) (RefNat 5)

spec :: ResidualSpec
spec = ResidualSpec
  { residualObligationId = ObligationId "audit.live-original"
  , residualOrigin = "phase1-audit-live-subject-continuity"
  , residualScope = "audit.original-subject"
  , residualRequiredPoint = "after unrestricted use"
  }

checkedLiteral :: Either String ValueResult
checkedLiteral = do
  result <- mapLeft show $ checkValue (VUInt 8 0) boundTy emptyCheckState
  assert (valueResultType result == boundTy) "wrong returned refined type"
  assert (valueResultTerm result == Just (RefUInt 8 0)) "wrong returned literal"
  pure result

fixture :: Either String (CheckState, Obligation, CheckState)
fixture = do
  literal <- checkedLiteral
  context <- mapLeft show $ insertBinding Unrestricted payload
    (valueResultType literal) (resourceContext emptyCheckState)
  let before = emptyCheckState { resourceContext = context }
  checked <- mapLeft show $
    checkValueWithResidual spec (VVar payload) targetTy before
  let after = valueResultState checked
  obligation <- maybe (Left "missing actual emitted residual") Right $
    Map.lookup (residualObligationId spec) (residualObligations after)
  assert (obligationProposition obligation == required) "wrong residual proposition"
  assert (resourceContext before == resourceContext after)
    "unrestricted binding changed during the actual value check"
  assert (Map.lookup payload (unrestrictedBindings (resourceContext after)) == Just boundTy)
    "original refined binding is not still present"
  pure (before, obligation, after)

checkStatic :: Obligation -> ResolvedObligation -> Either String ()
checkStatic obligation result = do
  assert (resolvedObligation result == obligation) "changed original obligation"
  assert (resolvedCanonicalProposition result == required) "changed requirement"
  assert (null (resolvedPrerequisites result)) "invented prerequisite"
  case resolvedDisposition result of
    StaticallyDischarged StaticByCertificate {} -> pure ()
    other -> Left ("expected exact arithmetic discharge, got " ++ show other)

testSupportMarksLiveUnrestricted :: Either String ()
testSupportMarksLiveUnrestricted = do
  (_, obligation, after) <- fixture
  support <- maybe (Left "missing durable logical subject support") Right $
    Map.lookup (obligationId obligation) (residualLogicalSubjects after)
  assert (logicalSupportBindings support == Map.singleton payload boundTy)
    "logical typing support changed the original subject type"
  assert (logicalSupportUnrestrictedBindings support == Map.singleton payload boundTy)
    "live unrestricted authority was not captured with the residual"

testBeforeSupportActivation :: Either String ()
testBeforeSupportActivation = do
  (before, obligation, _) <- fixture
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext before emptyDischargePolicy obligation
  checkStatic obligation resolved

testLiveOriginalAfterResidual :: Either String ()
testLiveOriginalAfterResidual = do
  (_, obligation, after) <- fixture
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext after emptyDischargePolicy obligation
  checkStatic obligation resolved

testOriginalProofStillWorks :: Either String ()
testOriginalProofStillWorks = do
  (before, obligation, after) <- fixture
  prior <- mapLeft show $
    resolveObligation emptyStaticContext before emptyDischargePolicy obligation
  checkStatic obligation prior
  context <- mapLeft show $ insertBinding Unrestricted proofName
    (TyProof (resolvedCanonicalProposition prior)) (resourceContext after)
  let withProof = after { resourceContext = context }
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext withProof emptyDischargePolicy obligation
  case resolvedDisposition resolved of
    StaticallyDischarged (StaticByEvidence actual) ->
      assert (actual == proofName) "selected the wrong supporting proof"
    other -> Left ("legitimate original proof stopped working: " ++ show other)

main :: IO ()
main = do
  rows <- sequence
    [ test "C01" "replacement-free fixture starts with genuinely checked refined zero" (checkedLiteral >> pure ())
    , test "C02" "original unrestricted binding survives exact residual emission" (fixture >> pure ())
    , test "C03" "residual records live unrestricted subject authority" testSupportMarksLiveUnrestricted
    , test "C04" "original bound proves requirement before support activation" testBeforeSupportActivation
    , test "C05" "genuinely established separately named original proof remains usable" testOriginalProofStillWorks
    , test "R01" "unchanged live original subject keeps its arithmetic evidence" testLiveOriginalAfterResidual
    ]
  unless (and rows) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label outcome =
  case outcome of
    Right () -> putStrLn ("PASS " ++ key ++ " " ++ label) >> pure True
    Left err -> putStrLn ("FAIL " ++ key ++ " " ++ label ++ " -- " ++ err) >> pure False

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
