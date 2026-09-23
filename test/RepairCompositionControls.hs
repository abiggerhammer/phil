{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Discharge (emptyDischargePolicy, resolveObligation)
import Phil.Core.Refinement (RefinementError (..), ResidualSpec (..))
import Phil.Core.SortCheck (checkTypeSorts)
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..), Name (..), Obligation (..), ObligationId (..)
  , ProductElementType (..), Proposition (..), RefTerm (..), Ty (..), Value (..) )
import Phil.Core.Value
  ( ValueError (..), ValueResult (..), checkValue, checkValueWithResidual, synthValue )
import System.Environment (getArgs)
import System.Exit (exitFailure)

partialTerm :: RefTerm
partialTerm = RefSub (RefNat 3) (RefNat 5)

badPredicate, safePredicate :: Proposition
badPredicate = Equal partialTerm partialTerm
safePredicate = Equal (RefSub (RefNat 5) (RefNat 3)) (RefSub (RefNat 5) (RefNat 3))

element :: Proposition -> Ty
element = TyRefined (Name "v") TyBool

productTy :: Proposition -> Ty
productTy predicate = TyProduct [ProductElementType Unrestricted (element predicate)]

nestedProductTy :: Proposition -> Ty
nestedProductTy predicate =
  TyProduct
    [ ProductElementType Affine
        (TyProduct [ProductElementType Linear (element predicate)])
    ]

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode name ty state = do
  context <- leftShow $ insertBinding mode name ty (resourceContext state)
  Right state { resourceContext = context }

productState :: Either String CheckState
productState = do
  -- Establish the field's legitimate inhabitation separately. The product
  -- binding is a supplied Core typing premise, not a fabricated source AST.
  _ <- leftShow $ checkValue (VBool True) (element Truth) emptyCheckState
  withBinding Unrestricted (Name "p") (productTy Truth) emptyCheckState

productResult :: Bool -> Either String (Either ValueError ValueResult)
productResult ascription = do
  state <- productState
  Right $ if ascription
    then synthValue (VAscribe (VVar (Name "p")) (productTy badPredicate)) state
    else checkValue (VVar (Name "p")) (productTy badPredicate) state

checkGap :: String -> Either ValueError ValueResult -> Either String ()
checkGap mode result = case (mode, result) of
  ("characterize", Right accepted)
    | valueResultType accepted == productTy badPredicate
      && Map.null (residualObligations (valueResultState accepted)) -> Right ()
  ("require-fix", Left (ValueRefinementError (StaticallyFalse _))) -> Right ()
  _ -> Left ("unexpected product definedness outcome: " ++ show result)

cases :: String -> [(String, Either String ())]
cases mode =
  [ ("R01", productResult False >>= checkGap mode)
  , ("R02", productResult True >>= checkGap mode)
  , ("H01", case checkValue (VBool True) (element badPredicate) emptyCheckState of
      Left (ValueRefinementError (StaticallyFalse _)) -> Right ()
      other -> Left ("direct bad refinement must reject: " ++ show other))
  , ("H02", do
      state <- productState
      result <- leftShow $ checkValue (VVar (Name "p")) (productTy safePredicate) state
      assert (valueResultType result == productTy safePredicate) "valid product not preserved")
  , ("H03", do
      state <- productState
      _ <- leftShow $ checkTypeSorts state (productTy badPredicate)
      Right ())
  , ("H04", do
      state <- productState
      result <- leftShow $ checkValue (VVar (Name "p")) (productTy Truth) state
      assert (valueResultType result == productTy Truth) "ordinary product equality broken")
  , ("H05", do
      state <- withBinding Linear (Name "payload") (TyBytes (RefNat 7)) emptyCheckState
      let target = TyRefined (Name "s") (TyBytes (RefNat 7))
            (Equal (RefVar (Name "s")) (RefVar (Name "s")))
      result <- leftShow $ checkValue (VVar (Name "payload")) target state
      assert (ownerAbsent (valueResultState result)) "logical view leaked owner availability")
  , ("H06", do
      -- A false predicate can describe a well-defined but uninhabited type.
      -- The supplied binding is a Core premise; definedness checking must not
      -- turn type formation into proof of the refinement proposition itself.
      state <- withBinding Unrestricted (Name "empty") (productTy Falsehood) emptyCheckState
      result <- leftShow $ checkValue (VVar (Name "empty")) (productTy Falsehood) state
      assert (valueResultType result == productTy Falsehood)
        "well-defined uninhabited refinement was rejected as ill-defined")
  , ("H07", do
      -- Preserve recursive product traversal and element modes while checking
      -- only the partial-operation prerequisites inside the refinement.
      state <- withBinding Unrestricted (Name "nested") (nestedProductTy Truth) emptyCheckState
      result <- leftShow $ checkValue (VVar (Name "nested")) (nestedProductTy safePredicate) state
      assert (valueResultType result == nestedProductTy safePredicate)
        "nested/mode-preserving valid product equality broken")
  ]

ownerAbsent :: CheckState -> Bool
ownerAbsent state = let context = resourceContext state in all (Map.notMember (Name "payload"))
  [unrestrictedBindings context, affineBindings context, linearBindings context]

-- Separately classified observation, not an invalid-acceptance regression.
-- Uses the returned residual and returned state without reconstructing either.
residualObservation :: Either String String
residualObservation = do
  state <- withBinding Linear (Name "payload") (TyBytes (RefNat 7)) emptyCheckState
  let predicate = LessEqual (RefNat 1) (RefLen (RefVar (Name "s")))
      target = TyRefined (Name "s") (TyBytes (RefNat 7)) predicate
      spec = ResidualSpec (ObligationId "n3.owner") "n3-origin" "n3-scope" "n3-point"
  result <- leftShow $ checkValueWithResidual spec (VVar (Name "payload")) target state
  assert (ownerAbsent (valueResultState result)) "residualization restored resource ownership"
  obligation <- maybe (Left "setup: missing emitted owner residual") Right $
    Map.lookup (ObligationId "n3.owner") (residualObligations (valueResultState result))
  assert (obligationProposition obligation == LessEqual (RefNat 1) (RefLen (RefVar (Name "payload"))))
    "emitted predicate lost exact owner subject"
  Right $ show $ resolveObligation emptyStaticContext (valueResultState result) emptyDischargePolicy obligation

main :: IO ()
main = do
  args <- getArgs
  mode <- case args of
    [chosen] | chosen `elem` ["characterize", "require-fix"] -> pure chosen
    _ -> putStrLn "usage: RepairCompositionControls.hs characterize|require-fix" >> exitFailure
  outcomes <- mapM run (cases mode)
  observed <- case residualObservation of
    Left err -> putStrLn ("OBS O01 SETUP_ERROR " ++ err) >> pure False
    Right value -> putStrLn ("OBS O01 RESULT " ++ value) >> pure True
  unless (and outcomes && observed) exitFailure
  where
    run (name, result) = case result of
      Right () -> putStrLn ("CHECK " ++ name ++ " PASS") >> pure True
      Left detail -> putStrLn ("CHECK " ++ name ++ " FAIL " ++ detail) >> pure False

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

leftShow :: Show e => Either e a -> Either String a
leftShow = either (Left . ("setup/operation: " ++) . show) Right
