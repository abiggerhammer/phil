{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
  ( CalleeTransition (PreserveCallee)
  )
import Phil.Core.CallableRefinement
  ( CallableMachineShape (..)
  )
import Phil.Core.CheckedUIntArithmetic
  ( checkedUIntArithmeticFailures
  , checkedUIntOverflowFailure
  , checkedUIntUnderflowFailure
  )
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (Unrestricted))
import Phil.Core.UIntArithmetic (UIntArithmeticOperator (..))
import Phil.Systems.CallableLowering
  ( CallableLoweringError (..)
  , CallableRealizationAccounting (..)
  , SourceCallableLoweringFacts (..)
  , TargetCallableLoweringFacts (..)
  , TargetCallableRepresentation (DirectCallable)
  , checkCallableLoweringCorrespondence
  )
import Phil.Systems.IR (emptyCostShape)
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-009 checked UInt operators expose exact typed-negative outcomes"
        exactCheckedFailureSurface
    , test "EXEC-009 CALL-016 lowering preserves checked overflow branch"
        checkedOverflowBranchPreserved
    , test "EXEC-009 CALL-016 lowering rejects erased checked overflow branch"
        checkedOverflowBranchCannotDisappear
    , test "EXEC-009 CALL-016 lowering rejects overflow/underflow branch substitution"
        checkedFailureIdentityCannotChange
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactCheckedFailureSurface :: Either String ()
exactCheckedFailureSurface = do
  assert
    (checkedUIntArithmeticFailures UIntAdd == Set.singleton checkedUIntOverflowFailure)
    "checked addition did not expose exactly uint-overflow"
  assert
    (checkedUIntArithmeticFailures UIntMultiply == Set.singleton checkedUIntOverflowFailure)
    "checked multiplication did not expose exactly uint-overflow"
  assert
    (checkedUIntArithmeticFailures UIntSubtract == Set.singleton checkedUIntUnderflowFailure)
    "checked subtraction did not expose exactly uint-underflow"

checkedOverflowBranchPreserved :: Either String ()
checkedOverflowBranchPreserved =
  case checkCallableLoweringCorrespondence sourceAddFacts targetAddFacts emptyAccounting of
    Right _ -> Right ()
    Left err -> Left ("CALL-016 rejected exact checked-outcome preservation: " <> show err)

checkedOverflowBranchCannotDisappear :: Either String ()
checkedOverflowBranchCannotDisappear =
  case checkCallableLoweringCorrespondence
      sourceAddFacts
      (targetAddFacts { targetCallableFailures = Set.empty })
      emptyAccounting of
    Left (CallableLoweringFailureMismatch expected actual) -> do
      assert
        (expected == checkedUIntArithmeticFailures UIntAdd)
        "failure-erasure rejection lost the source checked overflow set"
      assert (Set.null actual)
        "failure-erasure rejection reported an unexpected target failure set"
    other -> Left
      ("backend erased the checked overflow branch without rejection: " <> show other)

checkedFailureIdentityCannotChange :: Either String ()
checkedFailureIdentityCannotChange =
  case checkCallableLoweringCorrespondence
      sourceAddFacts
      (targetAddFacts
        { targetCallableFailures = checkedUIntArithmeticFailures UIntSubtract
        })
      emptyAccounting of
    Left (CallableLoweringFailureMismatch expected actual) -> do
      assert
        (expected == Set.singleton checkedUIntOverflowFailure)
        "failure-identity rejection lost uint-overflow"
      assert
        (actual == Set.singleton checkedUIntUnderflowFailure)
        "failure-identity rejection lost substituted uint-underflow"
    other -> Left
      ("backend substituted underflow for overflow without rejection: " <> show other)

sourceAddFacts :: SourceCallableLoweringFacts
sourceAddFacts = SourceCallableLoweringFacts
  { sourceCallableContractRevision = InterfaceRevision "exec009.checked-add.v1"
  , sourceCallableMachineShape = CallableMachineShape "fn(U8,U8)->checked-U8"
  , sourceCallableOccurrence = Nothing
  , sourceCallableStructuralMode = Unrestricted
  , sourceCallableCaptures = Map.empty
  , sourceCallableCalleeTransition = PreserveCallee
  , sourceCallableCallerAuthority = Set.empty
  , sourceCallableInternalAuthority = Set.empty
  , sourceCallableEffectBound = Set.empty
  , sourceCallableFailures = checkedUIntArithmeticFailures UIntAdd
  , sourceCallableLiveLoans = Set.empty
  }

targetAddFacts :: TargetCallableLoweringFacts
targetAddFacts = TargetCallableLoweringFacts
  { targetCallableRepresentation = DirectCallable
  , targetCallableRepresentationIdentity = Just "exec009.checked-add"
  , targetCallableContractRevision = sourceCallableContractRevision sourceAddFacts
  , targetCallableMachineShape = sourceCallableMachineShape sourceAddFacts
  , targetCallableOccurrence = sourceCallableOccurrence sourceAddFacts
  , targetCallableStructuralMode = sourceCallableStructuralMode sourceAddFacts
  , targetCallableCaptures = sourceCallableCaptures sourceAddFacts
  , targetCallableCalleeTransition = sourceCallableCalleeTransition sourceAddFacts
  , targetCallableCallerAuthority = sourceCallableCallerAuthority sourceAddFacts
  , targetCallableInternalAuthority = sourceCallableInternalAuthority sourceAddFacts
  , targetCallableEffectBound = sourceCallableEffectBound sourceAddFacts
  , targetCallableFailures = sourceCallableFailures sourceAddFacts
  , targetCallableLiveLoans = sourceCallableLiveLoans sourceAddFacts
  , targetCallableIntroducedEffects = Set.empty
  , targetCallableIntroducedFailures = Set.empty
  , targetCallableIntroducedAssumptions = Set.empty
  , targetCallableIntroducedCarriers = Set.empty
  , targetCallableIntroducedCost = emptyCostShape
  }

emptyAccounting :: CallableRealizationAccounting
emptyAccounting = CallableRealizationAccounting
  { accountedCallableEffects = Set.empty
  , accountedCallableFailures = Set.empty
  , accountedCallableAssumptions = Set.empty
  , accountedCallableCarriers = Set.empty
  , accountedCallableCost = emptyCostShape
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
