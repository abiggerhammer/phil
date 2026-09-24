{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Discharge
  ( ObligationDisposition (..), ResolvedObligation (..), StaticDischarge (..)
  , emptyDischargePolicy, resolveObligation )
import Phil.Core.Refinement (ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..), Name (..), Obligation (..), ObligationId (..)
  , Proposition (..), RefTerm (..), Ty (..), Value (..) )
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual)
import System.Exit (exitFailure)

-- Binding insertion is an explicit Core-environment adapter. The literal's
-- refined type is obtained from the real value checker, not fabricated.
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
  , residualOrigin = "independent-live-subject-preservation"
  , residualScope = "audit.original-subject"
  , residualRequiredPoint = "after unrestricted use"
  }

checkedLiteral :: Either String ValueResult
checkedLiteral = do
  result <- mapLeft show $ checkValue (VUInt 8 0) boundTy emptyCheckState
  ensure (valueResultType result == boundTy) "wrong returned refined type"
  ensure (valueResultTerm result == Just (RefUInt 8 0)) "wrong returned literal"
  pure result

fixture :: Either String (CheckState, Obligation, CheckState)
fixture = do
  literal <- checkedLiteral
  context <- mapLeft show $ insertBinding Unrestricted payload
    (valueResultType literal) (resourceContext emptyCheckState)
  let before = emptyCheckState { resourceContext = context }
  checked <- mapLeft show $ checkValueWithResidual spec (VVar payload) targetTy before
  let after = valueResultState checked
  obligation <- maybe (Left "missing actual emitted residual") Right $
    Map.lookup (residualObligationId spec) (residualObligations after)
  ensure (obligationProposition obligation == required) "wrong residual proposition"
  ensure (resourceContext before == resourceContext after)
    "unrestricted binding changed during the actual value check"
  ensure (Map.lookup payload (unrestrictedBindings (resourceContext after)) == Just boundTy)
    "original refined binding is not still present"
  pure (before, obligation, after)

checkStatic :: Obligation -> ResolvedObligation -> Either String ()
checkStatic obligation result = do
  ensure (resolvedObligation result == obligation) "changed original obligation"
  ensure (resolvedCanonicalProposition result == required) "changed requirement"
  ensure (null (resolvedPrerequisites result)) "invented prerequisite"
  case resolvedDisposition result of
    StaticallyDischarged StaticByCertificate {} -> pure ()
    other -> Left ("expected exact arithmetic discharge, got " ++ show other)

c01, c02, c03, c04, r01 :: Either String ()
c01 = checkedLiteral >> pure ()
c02 = fixture >> pure ()
c03 = do
  (before, obligation, _) <- fixture
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext before emptyDischargePolicy obligation
  checkStatic obligation resolved

-- A genuine earlier resolver success supplies this explicit named-proof
-- premise. This adapter is not an immutable assurance-evidence exporter.
c04 = do
  (before, obligation, after) <- fixture
  prior <- mapLeft show $
    resolveObligation emptyStaticContext before emptyDischargePolicy obligation
  checkStatic obligation prior
  context <- mapLeft show $ insertBinding Unrestricted proofName
    (TyProof (resolvedCanonicalProposition prior)) (resourceContext after)
  let withProof = after { resourceContext = context }
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext withProof emptyDischargePolicy obligation
  ensure (resolvedObligation resolved == obligation) "proof changed the obligation"
  case resolvedDisposition resolved of
    StaticallyDischarged (StaticByEvidence actual) ->
      ensure (actual == proofName) "selected the wrong supporting proof"
    other -> Left ("legitimate original proof stopped working: " ++ show other)

-- No scope exit, consumption, replacement or rebinding occurs in this case.
-- Adding durable interpretation must not suppress this original value's fact.
r01 = do
  (_, obligation, after) <- fixture
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext after emptyDischargePolicy obligation
  checkStatic obligation resolved

main :: IO ()
main = do
  rows <- sequence
    [ test "C01" checkedLiteralLabel c01
    , test "C02" "original unrestricted binding survives exact residual emission" c02
    , test "C03" "original bound proves requirement before support activation" c03
    , test "C04" "genuinely established separately named original proof remains usable" c04
    , test "R01" "unchanged live original subject keeps its arithmetic evidence" r01
    ]
  case fixture of
    Left err -> putStrLn ("OBS_SETUP_ERROR O01 " ++ err)
    Right (_, obligation, after) -> putStrLn $ "OBS O01 " ++ show
      (resolveObligation emptyStaticContext after emptyDischargePolicy obligation)
  putStrLn "COMPLETE correctness_groups=5 observations=1"
  unless (and rows) exitFailure
  where
    checkedLiteralLabel = "replacement-free fixture starts with genuinely checked refined zero"

test :: String -> String -> Either String () -> IO Bool
test key label outcome = case outcome of
  Right () -> putStrLn ("PASS " ++ key ++ " " ++ label) >> pure True
  Left err -> putStrLn ("FAIL " ++ key ++ " " ++ label ++ " -- " ++ err) >> pure False

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False message = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
