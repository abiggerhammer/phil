{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Generic
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "GEN-001 structure-polymorphic identity requires neither weakening nor contraction" structurePolymorphicIdentity
    , test "GEN-001 linear actual satisfies pure transfer" linearActualSatisfiesTransfer
    , test "GEN-002 discard induces weakening" discardInducesWeakening
    , test "GEN-002 affine and unrestricted actuals satisfy weakening" weakeningModeRelation
    , test "GEN-002 linear actual rejects inferred weakening" linearRejectsWeakening
    , test "GEN-003 duplication induces contraction" duplicationInducesContraction
    , test "GEN-003 only unrestricted actual satisfies contraction" contractionModeRelation
    , test "combined duplicate and discard requires both structural permissions" combinedRequirements
    , test "requirement inference is canonical under use ordering" useOrderingIsNonsemantic
    , test "distinct abstract parameters retain independent requirements" parameterRequirementsRemainIndependent
    , test "unknown abstract value use rejects" unknownParameterRejects
    , test "duplicate abstract value parameter identity rejects" duplicateParameterRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

structurePolymorphicIdentity :: Either String ()
structurePolymorphicIdentity = do
  requirements <- requirementsFor [TransferGenericValue valueT]
  assert
    (genericStructuralPermissions requirements == Set.empty)
    "pure transfer inferred a structural privilege"

linearActualSatisfiesTransfer :: Either String ()
linearActualSatisfiesTransfer = do
  requirements <- requirementsFor [TransferGenericValue valueT]
  mapLeft show (checkGenericStructuralActual valueT Linear requirements)

discardInducesWeakening :: Either String ()
discardInducesWeakening = do
  requirements <- requirementsFor [DiscardGenericValue valueT]
  assert
    (genericStructuralPermissions requirements == Set.singleton WeakeningPermission)
    "discard did not infer exactly weakening"

weakeningModeRelation :: Either String ()
weakeningModeRelation = do
  requirements <- requirementsFor [DiscardGenericValue valueT]
  mapLeft show (checkGenericStructuralActual valueT Affine requirements)
  mapLeft show (checkGenericStructuralActual valueT Unrestricted requirements)

linearRejectsWeakening :: Either String ()
linearRejectsWeakening = do
  requirements <- requirementsFor [DiscardGenericValue valueT]
  case checkGenericStructuralActual valueT Linear requirements of
    Left (MissingStructuralPermission key WeakeningPermission Linear) ->
      assert (key == valueT) "weakening rejection named the wrong parameter"
    other -> Left ("linear actual unexpectedly satisfied weakening: " <> show other)

duplicationInducesContraction :: Either String ()
duplicationInducesContraction = do
  requirements <- requirementsFor [DuplicateGenericValue valueT]
  assert
    (genericStructuralPermissions requirements == Set.singleton ContractionPermission)
    "duplication did not infer exactly contraction"

contractionModeRelation :: Either String ()
contractionModeRelation = do
  requirements <- requirementsFor [DuplicateGenericValue valueT]
  mapLeft show (checkGenericStructuralActual valueT Unrestricted requirements)
  expectMissing ContractionPermission Affine requirements
  expectMissing ContractionPermission Linear requirements

combinedRequirements :: Either String ()
combinedRequirements = do
  requirements <- requirementsFor
    [DuplicateGenericValue valueT, DiscardGenericValue valueT]
  assert
    (genericStructuralPermissions requirements
      == Set.fromList [WeakeningPermission, ContractionPermission])
    "combined body uses did not retain both structural requirements"
  mapLeft show (checkGenericStructuralActual valueT Unrestricted requirements)
  expectAnyMissing Affine requirements
  expectAnyMissing Linear requirements

useOrderingIsNonsemantic :: Either String ()
useOrderingIsNonsemantic = do
  first <- requirementsFor
    [ TransferGenericValue valueT
    , DuplicateGenericValue valueT
    , DiscardGenericValue valueT
    ]
  second <- requirementsFor
    [ DiscardGenericValue valueT
    , TransferGenericValue valueT
    , DuplicateGenericValue valueT
    ]
  assert (first == second) "use event ordering changed the canonical requirement set"

parameterRequirementsRemainIndependent :: Either String ()
parameterRequirementsRemainIndependent = do
  result <- mapLeft show $ inferGenericStructuralRequirements
    [valueT, valueU]
    [DiscardGenericValue valueT, DuplicateGenericValue valueU]
  tRequirements <- requireRequirements valueT result
  uRequirements <- requireRequirements valueU result
  assert
    (genericStructuralPermissions tRequirements == Set.singleton WeakeningPermission)
    "T requirement leaked or changed"
  assert
    (genericStructuralPermissions uRequirements == Set.singleton ContractionPermission)
    "U requirement leaked or changed"

unknownParameterRejects :: Either String ()
unknownParameterRejects =
  case inferGenericStructuralRequirements
      [valueT]
      [TransferGenericValue valueU] of
    Left (UnknownGenericValueParameter key) ->
      assert (key == valueU) "unknown-use rejection named the wrong parameter"
    other -> Left ("unknown generic value use did not reject: " <> show other)

duplicateParameterRejects :: Either String ()
duplicateParameterRejects =
  case inferGenericStructuralRequirements [valueT, valueT] [] of
    Left (DuplicateGenericValueParameter key) ->
      assert (key == valueT) "duplicate-parameter rejection named the wrong key"
    other -> Left ("duplicate generic value parameter did not reject: " <> show other)

requirementsFor :: [GenericStructuralUse] -> Either String GenericStructuralRequirements
requirementsFor uses = do
  result <- mapLeft show $ inferGenericStructuralRequirements [valueT] uses
  requireRequirements valueT result

requireRequirements
  :: GenericValueParameterKey
  -> Map.Map GenericValueParameterKey GenericStructuralRequirements
  -> Either String GenericStructuralRequirements
requireRequirements key requirements = maybe
  (Left ("missing structural requirements for " <> show key))
  Right
  (Map.lookup key requirements)

expectMissing
  :: StructuralPermission
  -> Mode
  -> GenericStructuralRequirements
  -> Either String ()
expectMissing permission mode requirements =
  case checkGenericStructuralActual valueT mode requirements of
    Left (MissingStructuralPermission key actualPermission actualMode) ->
      assert
        (key == valueT && actualPermission == permission && actualMode == mode)
        "structural rejection did not preserve exact parameter/permission/mode"
    other -> Left ("missing structural permission did not reject: " <> show other)

expectAnyMissing
  :: Mode
  -> GenericStructuralRequirements
  -> Either String ()
expectAnyMissing mode requirements =
  case checkGenericStructuralActual valueT mode requirements of
    Left (MissingStructuralPermission key _ actualMode) ->
      assert (key == valueT && actualMode == mode)
        "combined structural rejection named the wrong parameter/mode"
    other -> Left ("restricted actual unexpectedly satisfied combined requirements: " <> show other)

valueT, valueU :: GenericValueParameterKey
valueT = GenericValueParameterKey "generic.value.T"
valueU = GenericValueParameterKey "generic.value.U"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
