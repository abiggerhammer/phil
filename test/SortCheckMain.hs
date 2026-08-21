{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Refinement (RefinementError (RefinementSortError))
import Phil.Core.SortCheck
  ( SortError (..)
  , checkPropositionSorts
  , sortOfRefTerm
  )
import Phil.Core.Syntax
  ( Mode (Unrestricted)
  , Name (Name)
  , Proposition (..)
  , RefSort (..)
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
    [ test "sorted opaque collection variables support membership" testCollectionVariable
    , test "stable-ID variables preserve identity kinds" testStableIdVariables
    , test "sorted opaque values check against their declared type" testSortedOpaqueValueType
    , test "sorted opaque variables expose their declared refinement sort" testSortedOpaqueSort
    , test "dependent Bytes indices must have Nat sort" testBytesIndexSort
    ]
  unless (and results) exitFailure

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

name :: String -> Name
name = Name . Text.pack

testCollectionVariable :: Either String ()
testCollectionVariable = do
  let collectionSort = SortFiniteSet (SortUInt 16)
      collectionTy = TyOpaqueSorted "SupportedVersions" collectionSort
  state <- withUnrestricted (name "serverSupported") collectionTy emptyCheckState
  mapLeft show $ checkPropositionSorts state
    (Member (RefUInt 16 7) (RefVar (name "serverSupported")))

testStableIdVariables :: Either String ()
testStableIdVariables = do
  state0 <- withUnrestricted
    (name "frameId")
    (TyOpaqueSorted "FrameIdentity" (SortStableId "Frame"))
    emptyCheckState
  state1 <- withUnrestricted
    (name "policyId")
    (TyOpaqueSorted "PolicyIdentity" (SortStableId "PolicySnapshot"))
    state0
  case checkPropositionSorts state1
    (Equal (RefVar (name "frameId")) (RefVar (name "policyId"))) of
    Left (EqualitySortMismatch (SortStableId "Frame") (SortStableId "PolicySnapshot")) -> Right ()
    other -> Left ("stable-ID variables lost their identity kinds: " ++ show other)

testSortedOpaqueValueType :: Either String ()
testSortedOpaqueValueType = do
  let ty = TyOpaqueSorted "SupportedVersions" (SortFiniteSet (SortUInt 16))
  state <- withUnrestricted (name "supported") ty emptyCheckState
  case checkValue (VVar (name "supported")) ty state of
    Right result
      | valueResultType result == ty -> Right ()
    other -> Left ("sorted opaque value did not check against itself: " ++ show other)

testSortedOpaqueSort :: Either String ()
testSortedOpaqueSort = do
  let sort = SortEnum "DigestAlgorithm"
      ty = TyOpaqueSorted "DigestAlgorithm" sort
  state <- withUnrestricted (name "alg") ty emptyCheckState
  actual <- mapLeft show $ sortOfRefTerm state (RefVar (name "alg"))
  assert (actual == sort) "sorted opaque variable exposed the wrong refinement sort"

testBytesIndexSort :: Either String ()
testBytesIndexSort = do
  let malformed = TyBytes (RefBool True)
  state <- withUnrestricted (name "payload") malformed emptyCheckState
  case checkValue (VVar (name "payload")) malformed state of
    Left (ValueRefinementError (RefinementSortError (InvalidBytesIndexSort (RefBool True) SortBool))) -> Right ()
    other -> Left ("ill-sorted Bytes index was accepted: " ++ show other)

withUnrestricted :: Name -> Ty -> CheckState -> Either String CheckState
withUnrestricted binding ty state = do
  context <- mapLeft show $ insertBinding Unrestricted binding ty (resourceContext state)
  Right (state { resourceContext = context })

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
