{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Refinement (RefinementError (..))
import Phil.Core.SortCheck (checkTypeSorts)
import Phil.Core.Syntax
  ( Mode (..), Name (..), ProductElementType (..), Proposition (..)
  , RefTerm (..), Ty (..), Value (..) )
import Phil.Core.Value
  ( ValueError (..), ValueResult (..), checkValue, synthValue )
import System.Exit (exitFailure)

partialTerm :: RefTerm
partialTerm = RefSub (RefNat 3) (RefNat 5)

badPredicate, safePredicate :: Proposition
badPredicate = Equal partialTerm partialTerm
safePredicate =
  Equal
    (RefSub (RefNat 5) (RefNat 3))
    (RefSub (RefNat 5) (RefNat 3))

element :: Proposition -> Ty
element = TyRefined (Name "v") TyBool

productTy :: Proposition -> Ty
productTy proposition =
  TyProduct [ProductElementType Unrestricted (element proposition)]

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode name ty state = do
  context <- leftShow $
    insertBinding mode name ty (resourceContext state)
  Right state { resourceContext = context }

productState :: Either String CheckState
productState = do
  -- Establish the field's legitimate inhabitation separately. The product
  -- binding is a supplied Core typing premise, not a fabricated source AST.
  _ <- leftShow $ checkValue (VBool True) (element Truth) emptyCheckState
  withBinding Unrestricted (Name "p") (productTy Truth) emptyCheckState

expectDefinednessRejection
  :: Either ValueError ValueResult
  -> Either String ()
expectDefinednessRejection result =
  case result of
    Left (ValueRefinementError (StaticallyFalse _)) -> Right ()
    other -> Left ("expected nested definedness rejection, got " ++ show other)

cases :: [(String, Either String ())]
cases =
  [ ("R01", do
      state <- productState
      expectDefinednessRejection $
        checkValue (VVar (Name "p")) (productTy badPredicate) state)
  , ("R02", do
      state <- productState
      expectDefinednessRejection $
        synthValue
          (VAscribe (VVar (Name "p")) (productTy badPredicate))
          state)
  , ("H01", expectDefinednessRejection $
      checkValue (VBool True) (element badPredicate) emptyCheckState)
  , ("H02", do
      state <- productState
      result <- leftShow $
        checkValue (VVar (Name "p")) (productTy safePredicate) state
      assert
        (valueResultType result == productTy safePredicate)
        "valid nested product refinement was not preserved"
      assert
        (Map.null (residualObligations (valueResultState result)))
        "valid nested product refinement left a residual")
  , ("H03", do
      state <- productState
      _ <- leftShow $ checkTypeSorts state (productTy badPredicate)
      Right ())
  , ("H04", do
      state <- productState
      result <- leftShow $
        checkValue (VVar (Name "p")) (productTy Truth) state
      assert
        (valueResultType result == productTy Truth)
        "ordinary product equality was broken")
  , ("H05", do
      state <- withBinding Linear (Name "payload") (TyBytes (RefNat 7)) emptyCheckState
      let target = TyRefined (Name "s") (TyBytes (RefNat 7))
            (Equal (RefVar (Name "s")) (RefVar (Name "s")))
      result <- leftShow $ checkValue (VVar (Name "payload")) target state
      assert
        (ownerAbsent (Name "payload") (valueResultState result))
        "logical definedness view leaked resource ownership")
  , ("H06", do
      -- Definedness is not inhabitance: an exact false refinement carries no
      -- partial-operation prerequisite and must not be rejected merely because
      -- the proposition itself is false.
      state <-
        withBinding
          Unrestricted
          (Name "empty")
          (productTy Falsehood)
          emptyCheckState
      result <- leftShow $
        checkValue (VVar (Name "empty")) (productTy Falsehood) state
      assert
        (valueResultType result == productTy Falsehood)
        "type-definedness checking incorrectly required predicate truth")
  ]

ownerAbsent :: Name -> CheckState -> Bool
ownerAbsent name state =
  let context = resourceContext state
  in all (Map.notMember name)
      [ unrestrictedBindings context
      , affineBindings context
      , linearBindings context
      ]

main :: IO ()
main = do
  outcomes <- mapM run cases
  unless (and outcomes) exitFailure
  where
    run (name, result) =
      case result of
        Right () ->
          putStrLn ("CHECK " ++ name ++ " PASS") >> pure True
        Left detail ->
          putStrLn ("CHECK " ++ name ++ " FAIL " ++ detail) >> pure False

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

leftShow :: Show e => Either e a -> Either String a
leftShow = either (Left . ("setup/operation: " ++) . show) Right
