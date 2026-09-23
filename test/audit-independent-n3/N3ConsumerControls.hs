{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Discharge
  ( DischargeError (..), ObligationDisposition (..), ResolvedObligation (..)
  , StaticDischarge (..), emptyDischargePolicy, resolveObligation )
import Phil.Core.NumericConversion
  ( NumericType (..), NumericValue (..), NumericConversionResult (..)
  , NumericConversionPrecision (..), convertNumericValue )
import Phil.Core.Refinement
  ( RefinementError (..), ResidualSpec (..), dischargeProposition )
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..), Name (..), Obligation (..), ObligationId (..)
  , Proposition (..), RefTerm (..), Ty (..), Value (..) )
import Phil.Core.Value (ValueError (..), ValueResult (..), checkValue, checkValueWithResidual)
import System.Exit (exitFailure)

-- AUDIT ADAPTER ONLY: not a discovered production compiler bridge.
-- Its output is constructed from the genuinely returned UInt payload, never
-- from an independently supplied expected magnitude.
convertedSeven :: Either String Value
convertedSeven = do
  result <- leftShow $ convertNumericValue (NumericUIntType 16) (NumericUIntValue 8 7)
  assert (numericConversionPrecision result == NumericConversionExact) "conversion lost exact precision"
  case numericConversionValue result of
    NumericUIntValue w v -> Right (VUInt w v)
    _ -> Left "setup: expected a UInt conversion result"

refinedSeven :: Ty
refinedSeven = TyRefined (Name "v") (TyUInt 16) (Equal (RefVar (Name "v")) (RefUInt 16 7))

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode name ty state = do
  context <- leftShow $ insertBinding mode name ty (resourceContext state)
  Right state { resourceContext = context }

absent :: Name -> CheckState -> Bool
absent n s = let c = resourceContext s in all (Map.notMember n)
  [unrestrictedBindings c, affineBindings c, linearBindings c]

checkConverted :: Either String ValueResult
checkConverted = do
  v <- convertedSeven
  leftShow $ checkValue v refinedSeven emptyCheckState

pendingFixture :: Either String (Proposition, Obligation, CheckState)
pendingFixture = do
  s <- withBinding Unrestricted (Name "r") (TyUInt 16) emptyCheckState
  let p = Equal (RefVar (Name "r")) (RefUInt 16 7)
      spec = ResidualSpec (ObligationId "n3.pending") "n3-origin" "n3-scope" "n3-point"
  result <- leftShow $ checkValueWithResidual spec (VVar (Name "r")) refinedSeven s
  o <- maybe (Left "setup: exact residual missing") Right $
    Map.lookup (ObligationId "n3.pending") (residualObligations (valueResultState result))
  assert (obligationProposition o == p) "pending proposition changed"
  Right (p, o, valueResultState result)

cases :: [(String, Either String ())]
cases =
  [ ("N01", do
      result <- checkConverted
      assert (valueResultType result == refinedSeven && valueResultTerm result == Just (RefUInt 16 7))
        "returned Core type/subject does not match actual converted result")
  , ("N02", do
      value <- convertedSeven
      let wrong = TyRefined (Name "v") (TyUInt 16) (Equal (RefVar (Name "v")) (RefUInt 16 8))
      case checkValue value wrong emptyCheckState of
        Left (ValueRefinementError (StaticallyFalse _)) -> Right ()
        other -> Left ("wrong result refinement: " ++ show other))
  , ("N03", case checkValue (VUInt 8 7) (TyUInt 16) emptyCheckState of
      Left (ValueTypeMismatch _ _) -> Right ()
      other -> Left ("width conversion silently assumed: " ++ show other))
  , ("N04", do
      number <- checkConverted
      term <- maybe (Left "setup: numeric result subject missing") Right (valueResultTerm number)
      state <- withBinding Linear (Name "bytes") (TyBytes (RefNat 7)) emptyCheckState
      result <- leftShow $ checkValue (VVar (Name "bytes")) (TyBytes (RefToNat term)) state
      assert (valueResultType result == TyBytes (RefToNat term)) "result index changed"
      assert (absent (Name "bytes") (valueResultState result)) "byte owner was not consumed")
  , ("N05", do
      number <- checkConverted
      term <- maybe (Left "setup: numeric result subject missing") Right (valueResultTerm number)
      state <- withBinding Linear (Name "bytes") (TyBytes (RefNat 8)) emptyCheckState
      case checkValue (VVar (Name "bytes")) (TyBytes (RefToNat term)) state of
        Left (ExplicitTransportRequired _ _) -> Right ()
        other -> Left ("different byte count did not require transport: " ++ show other))
  , ("N06", do
      (_, o, state) <- pendingFixture
      assert (obligationOrigin o == "n3-origin" && obligationScope o == "n3-scope"
        && obligationRequiredPoint o == "n3-point") "residual provenance changed"
      assert (Map.size (residualObligations state) == 1) "extra or missing pending record")
  , ("N07", do
      (p, _, state) <- pendingFixture
      case dischargeProposition p state of
        Left (MissingEvidence actual) | actual == p -> Right ()
        other -> Left ("pending record became proof: " ++ show other))
  , ("N08", do
      (p, o, state) <- pendingFixture
      case resolveObligation emptyStaticContext state emptyDischargePolicy o of
        Left (UnresolvedObligation oid actual)
          | oid == obligationId o && actual == p -> Right ()
        other -> Left ("unproved pending relation resolved: " ++ show other))
  , ("N09", do
      (p, o, state) <- pendingFixture
      -- Explicit legitimate fixture premise; no claim this is a production exporter.
      supported <- withBinding Unrestricted (Name "evidence") (TyProof p) state
      resolved <- leftShow $ resolveObligation emptyStaticContext supported emptyDischargePolicy o
      assert (resolvedObligation resolved == o) "resolver changed original obligation"
      case resolvedDisposition resolved of
        StaticallyDischarged (StaticByEvidence (Name "evidence")) -> Right ()
        other -> Left ("expected exact supplied proof binding, got " ++ show other))
  , ("N10", do
      (p, o, state) <- pendingFixture
      supported <- withBinding Unrestricted (Name "evidence") (TyProof p) state
      _ <- leftShow $ resolveObligation emptyStaticContext supported emptyDischargePolicy o
      -- The per-record resolver is pure and does not return an updated CheckState.
      assert (Map.lookup (obligationId o) (residualObligations supported) == Just o)
        "input pending record changed")
  , ("N11", do
      (p, _, state) <- pendingFixture
      -- A true closed arithmetic fact is not a fact about arbitrary r.
      let closed = Equal (RefAdd (RefNat 3) (RefNat 4)) (RefNat 7)
      supported <- withBinding Unrestricted (Name "closed") (TyProof closed) state
      case dischargeProposition p supported of
        Left (MissingEvidence actual) | actual == p -> Right ()
        other -> Left ("unrelated closed fact authorized named result: " ++ show other))
  , ("N12", do
      r <- checkConverted
      assert (Map.null (residualObligations (valueResultState r))) "closed exact value left a residual")
  ]

main :: IO ()
main = do
  outcomes <- mapM run cases
  unless (and outcomes) exitFailure
  where
    run (name, result) = case result of
      Right () -> putStrLn ("CHECK " ++ name ++ " PASS") >> pure True
      Left detail -> putStrLn ("CHECK " ++ name ++ " FAIL " ++ detail) >> pure False

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message
leftShow :: Show e => Either e a -> Either String a
leftShow = either (Left . ("setup/operation: " ++) . show) Right
