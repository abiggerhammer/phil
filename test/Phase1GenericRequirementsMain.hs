{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Generic
  ( CheckedGenericStructuralInterface (..)
  , GenericStructuralError (..)
  , GenericStructuralRequirements (..)
  , GenericStructuralUse (..)
  , GenericValueParameterKey (..)
  , StructuralPermission (..)
  , checkGenericStructuralInterface
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "GEN-004 body uses induce the exact minimum requirement set" exactMinimumRequirements
    , test "GEN-004 requirement inference is independent of use ordering" useOrderingDoesNotMatter
    , test "GEN-005 a public contract may intentionally be stronger" strongerPublishedContractAccepted
    , test "GEN-005 body evolution within a stabilized contract is accepted" bodyEvolutionWithinContract
    , test "GEN-006 body requirements may not exceed the published interface" bodyCannotOutgrowPublishedContract
    , test "GEN-006 omitted published permission is semantically empty" omittedPublishedPermissionIsEmpty
    , test "generic public requirements reject unknown parameters" unknownPublishedParameterRejects
    , test "generic public requirements reject duplicate parameter entries" duplicatePublishedParameterRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactMinimumRequirements :: Either String ()
exactMinimumRequirements = do
  checked <- mapLeft show $ checkGenericStructuralInterface
    [t, u, v]
    [ TransferGenericValue t
    , DiscardGenericValue u
    , DuplicateGenericValue v
    ]
    Nothing
  assert
    (genericInducedStructuralRequirements checked == Map.fromList
      [ (t, requirements [])
      , (u, requirements [WeakeningPermission])
      , (v, requirements [ContractionPermission])
      ])
    "inferred minimum did not match the exact structural uses"
  assert
    (genericPublishedStructuralRequirements checked
      == genericInducedStructuralRequirements checked)
    "unstabilized interface did not publish the exact inferred minimum"

useOrderingDoesNotMatter :: Either String ()
useOrderingDoesNotMatter = do
  first <- mapLeft show $ checkGenericStructuralInterface
    [t, u]
    [DiscardGenericValue t, DuplicateGenericValue t, TransferGenericValue u]
    Nothing
  second <- mapLeft show $ checkGenericStructuralInterface
    [u, t]
    [TransferGenericValue u, DuplicateGenericValue t, DiscardGenericValue t]
    Nothing
  assert (first == second)
    "canonical generic requirements depended on declaration/use ordering"

strongerPublishedContractAccepted :: Either String ()
strongerPublishedContractAccepted = do
  checked <- mapLeft show $ checkGenericStructuralInterface
    [t]
    [TransferGenericValue t]
    (Just [(t, requirements [WeakeningPermission, ContractionPermission])])
  assert
    (Map.lookup t (genericInducedStructuralRequirements checked)
      == Just (requirements []))
    "transfer unexpectedly induced a structural privilege"
  assert
    (Map.lookup t (genericPublishedStructuralRequirements checked)
      == Just (requirements [WeakeningPermission, ContractionPermission]))
    "explicit stronger public requirement was not preserved"

bodyEvolutionWithinContract :: Either String ()
bodyEvolutionWithinContract = do
  original <- mapLeft show $ checkGenericStructuralInterface
    [t]
    [TransferGenericValue t]
    publicWeakening
  revised <- mapLeft show $ checkGenericStructuralInterface
    [t]
    [DiscardGenericValue t]
    publicWeakening
  assert
    (genericPublishedStructuralRequirements original
      == genericPublishedStructuralRequirements revised)
    "body evolution changed the stabilized public requirement set"
  assert
    (genericInducedStructuralRequirements original
      /= genericInducedStructuralRequirements revised)
    "body evolution did not change the inferred minimum"
  where
    publicWeakening = Just [(t, requirements [WeakeningPermission])]

bodyCannotOutgrowPublishedContract :: Either String ()
bodyCannotOutgrowPublishedContract =
  case checkGenericStructuralInterface
      [t]
      [DuplicateGenericValue t]
      (Just [(t, requirements [WeakeningPermission])]) of
    Left (PublishedStructuralRequirementTooWeak key permission) ->
      assert
        (key == t && permission == ContractionPermission)
        "wrong missing public structural permission reported"
    other -> Left ("body silently exceeded published interface: " <> show other)

omittedPublishedPermissionIsEmpty :: Either String ()
omittedPublishedPermissionIsEmpty =
  case checkGenericStructuralInterface
      [t]
      [DiscardGenericValue t]
      (Just []) of
    Left (PublishedStructuralRequirementTooWeak key permission) ->
      assert
        (key == t && permission == WeakeningPermission)
        "wrong omitted public requirement reported"
    other -> Left ("omitted public requirement did not mean empty: " <> show other)

unknownPublishedParameterRejects :: Either String ()
unknownPublishedParameterRejects =
  case checkGenericStructuralInterface
      [t]
      [TransferGenericValue t]
      (Just [(u, requirements [])]) of
    Left (UnknownPublishedGenericValueParameter key) ->
      assert (key == u) "wrong unknown published parameter reported"
    other -> Left ("unknown published parameter did not reject: " <> show other)

duplicatePublishedParameterRejects :: Either String ()
duplicatePublishedParameterRejects =
  case checkGenericStructuralInterface
      [t]
      [TransferGenericValue t]
      (Just
        [ (t, requirements [WeakeningPermission])
        , (t, requirements [WeakeningPermission, ContractionPermission])
        ]) of
    Left (DuplicatePublishedStructuralRequirement key) ->
      assert (key == t) "wrong duplicate published parameter reported"
    other -> Left ("duplicate published parameter did not reject: " <> show other)

requirements :: [StructuralPermission] -> GenericStructuralRequirements
requirements = GenericStructuralRequirements . Set.fromList

t, u, v :: GenericValueParameterKey
t = GenericValueParameterKey "T"
u = GenericValueParameterKey "U"
v = GenericValueParameterKey "V"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
