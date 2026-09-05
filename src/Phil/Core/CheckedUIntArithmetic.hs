{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.CheckedUIntArithmetic
  ( CheckedUIntOperand (..)
  , CheckedUIntArithmeticSuccess (..)
  , CheckedUIntArithmeticDecision (..)
  , CheckedUIntArithmeticError (..)
  , checkedUIntOverflowFailure
  , checkedUIntUnderflowFailure
  , checkedUIntArithmeticFailures
  , checkCheckedUIntArithmetic
  ) where

import qualified Data.Set as Set
import Phil.Core.CallableRefinement
  ( CallableFailure (..)
  )
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , scalarLiteralInRange
  )
import Phil.Core.Syntax
  ( Outcome (..)
  , Proposition
  , RefTerm (..)
  )
import Phil.Core.UIntArithmetic
  ( UIntArithmeticOperator (..)
  , applyUIntArithmeticOperator
  , plainUIntArithmeticProposition
  )

-- | Operand position is retained in fail-closed diagnostics; checked arithmetic
-- never repairs a wrong-width or non-UInt operand by coercion.
data CheckedUIntOperand
  = CheckedUIntLeftOperand
  | CheckedUIntRightOperand
  deriving (Eq, Ord, Show)

-- | A checked-success result carries both the exact runtime scalar and the
-- canonical arithmetic proposition established by the concrete operation.
-- The ScalarUIntLiteral constructor plus the range check below establish that
-- the mathematical result is representable in the exact UInt width.
data CheckedUIntArithmeticSuccess = CheckedUIntArithmeticSuccess
  { checkedUIntArithmeticResult :: ScalarLiteral
  , checkedUIntArithmeticExactProposition :: Proposition
  }
  deriving (Eq, Show)

-- | Runtime-contingent range failure is an ordinary typed-negative callable
-- outcome, not a trap, wraparound value, unresolved static obligation, or target
-- exception. Success remains the ordinary callable success branch.
data CheckedUIntArithmeticDecision
  = CheckedUIntArithmeticSucceeded CheckedUIntArithmeticSuccess
  | CheckedUIntArithmeticNegative CallableFailure
  deriving (Eq, Show)

data CheckedUIntArithmeticError
  = CheckedUIntArithmeticInvalidWidth Int
  | CheckedUIntArithmeticOperandTypeMismatch
      CheckedUIntOperand
      ScalarLiteral
      Int
  | CheckedUIntArithmeticOperandOutOfRange
      CheckedUIntOperand
      ScalarLiteral
  deriving (Eq, Show)

checkedUIntOverflowFailure :: CallableFailure
checkedUIntOverflowFailure = CallableTypedNegative (Outcome "uint-overflow")

checkedUIntUnderflowFailure :: CallableFailure
checkedUIntUnderflowFailure = CallableTypedNegative (Outcome "uint-underflow")

-- | Exact public negative-outcome surface for the three Phase-1 checked UInt
-- operations. Addition and multiplication can overflow; subtraction can
-- underflow. No implicit target failure is part of this source contract.
checkedUIntArithmeticFailures
  :: UIntArithmeticOperator
  -> Set.Set CallableFailure
checkedUIntArithmeticFailures operator = Set.singleton $ case operator of
  UIntAdd -> checkedUIntOverflowFailure
  UIntSubtract -> checkedUIntUnderflowFailure
  UIntMultiply -> checkedUIntOverflowFailure

-- | Evaluate one explicit checked UInt operation over concrete runtime values.
-- Mathematical arithmetic is shared with the plain EXEC-008 judgment and uses
-- unbounded Integer. An out-of-range mathematical result selects the declared
-- typed-negative branch instead of producing wraparound, saturation, UB, or a
-- target trap.
checkCheckedUIntArithmetic
  :: UIntArithmeticOperator
  -> Int
  -> ScalarLiteral
  -> ScalarLiteral
  -> Either CheckedUIntArithmeticError CheckedUIntArithmeticDecision
checkCheckedUIntArithmetic operator width leftLiteral rightLiteral = do
  if width > 0
    then Right ()
    else Left (CheckedUIntArithmeticInvalidWidth width)
  left <- operandValue CheckedUIntLeftOperand leftLiteral
  right <- operandValue CheckedUIntRightOperand rightLiteral
  let mathematicalResult = applyUIntArithmeticOperator operator left right
      resultLiteral = ScalarUIntLiteral width mathematicalResult
  if scalarLiteralInRange resultLiteral
    then
      let leftTerm = RefUInt width left
          rightTerm = RefUInt width right
          resultTerm = RefUInt width mathematicalResult
      in Right (CheckedUIntArithmeticSucceeded CheckedUIntArithmeticSuccess
          { checkedUIntArithmeticResult = resultLiteral
          , checkedUIntArithmeticExactProposition =
              plainUIntArithmeticProposition
                operator width leftTerm rightTerm resultTerm
          })
    else Right (CheckedUIntArithmeticNegative (rangeFailure operator mathematicalResult))
  where
    operandValue side literal = case literal of
      ScalarUIntLiteral actualWidth value
        | actualWidth /= width ->
            Left (CheckedUIntArithmeticOperandTypeMismatch side literal width)
        | not (scalarLiteralInRange literal) ->
            Left (CheckedUIntArithmeticOperandOutOfRange side literal)
        | otherwise -> Right value
      _ -> Left (CheckedUIntArithmeticOperandTypeMismatch side literal width)

rangeFailure :: UIntArithmeticOperator -> Integer -> CallableFailure
rangeFailure operator mathematicalResult = case operator of
  UIntSubtract
    | mathematicalResult < 0 -> checkedUIntUnderflowFailure
  _ -> checkedUIntOverflowFailure
