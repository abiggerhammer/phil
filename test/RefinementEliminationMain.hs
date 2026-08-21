{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Refinement
  ( EvidenceUse (..)
  , RefinementError (MissingEvidence)
  )
import Phil.Core.Syntax
  ( Mode (Unrestricted)
  , Name (Name)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  , Value (VVar)
  )
import Phil.Core.Value
  ( ValueError (ValueRefinementError)
  , ValueResult (..)
  , checkValue
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "refined values erase canonically to their base type" testRefinementElimination
    , test "unrestricted refined bindings entail their instantiated refinement" testRefinedBindingEvidence
    , test "refined binding evidence remains subject-specific" testRefinedBindingSubjectIdentity
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

var :: Text -> RefTerm
var = RefVar . name

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testRefinementElimination :: Either String ()
testRefinementElimination = do
  let refined = TyRefined
        (name "x")
        (TyUInt 16)
        (Atom "Allowed" [var "x"])
  state <- bind (name "selected") refined emptyCheckState
  result <- mapLeft show $ checkValue (VVar (name "selected")) (TyUInt 16) state
  assert (valueResultType result == TyUInt 16) "refined value did not erase to its base type"

testRefinedBindingEvidence :: Either String ()
testRefinedBindingEvidence = do
  let selectedTy = TyRefined
        (name "v")
        (TyUInt 16)
        (Member (var "v") (RefField (var "hello") "versions"))
      requiredTy = TyRefined
        (name "x")
        (TyUInt 16)
        (Member (var "x") (RefField (var "hello") "versions"))
  state <- bind (name "selected") selectedTy emptyCheckState
  result <- mapLeft show $ checkValue (VVar (name "selected")) requiredTy state
  assert
    (EvidenceByBinding
      (name "selected")
      (Member (var "selected") (RefField (var "hello") "versions"))
      `elem` valueResultEvidence result)
    "the refined binding did not supply its own instantiated evidence"

testRefinedBindingSubjectIdentity :: Either String ()
testRefinedBindingSubjectIdentity = do
  let selectedTy = TyRefined
        (name "v")
        (TyUInt 16)
        (Atom "Allowed" [var "v"])
      otherTy = TyRefined
        (name "x")
        (TyUInt 16)
        (Atom "Allowed" [var "x"])
  state0 <- bind (name "selected") selectedTy emptyCheckState
  state1 <- bind (name "other") (TyUInt 16) state0
  case checkValue (VVar (name "other")) otherTy state1 of
    Left (ValueRefinementError (MissingEvidence (Atom "Allowed" [RefVar subject]))) ->
      assert (subject == name "other") "missing-evidence proposition lost the actual subject"
    other -> Left ("refined evidence for another subject was accepted: " ++ show other)

bind :: Name -> Ty -> CheckState -> Either String CheckState
bind binding ty state = do
  context <- mapLeft show $ insertBinding Unrestricted binding ty (resourceContext state)
  Right (state { resourceContext = context })

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
