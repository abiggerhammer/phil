module Phil.Surface.GrammarV1.NumericConversion
  ( GrammarV1NumericEnvironment
  , GrammarV1NumericEvaluationError (..)
  , evaluateGrammarV1NumericExpression
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Phil.Core.FloatArithmetic
  ( FloatOperator (..)
  , FloatSemanticError
  , FloatValue
  , applyFloatOperator
  , floatFormat
  , negateFloatValue
  )
import Phil.Core.IntegerDivision
  ( IntegerDivisionOperator (..)
  , signedQuotientRemainder
  )
import Phil.Core.IntegerShift
  ( IntegerShiftError
  , IntegerShiftOperator (..)
  , applySIntShift
  , applyUIntShift
  )
import Phil.Core.NumericConversion
  ( NumericConversionError
  , NumericConversionResult (..)
  , NumericType (..)
  , NumericValue (..)
  , convertNumericValue
  , numericTypeFromCoreType
  , numericValueType
  )
import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntType
  , applySIntArithmeticOperator
  , sIntLiteralInRange
  , SIntArithmeticOperator (..)
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BinaryOperator (..)
  , GrammarV1Expression (..)
  , GrammarV1ShiftOperator (..)
  , GrammarV1StaticReference
  )
import Phil.Surface.Syntax (Located (..))

type GrammarV1NumericEnvironment = Map GrammarV1StaticReference NumericValue

data GrammarV1NumericEvaluationError
  = GrammarV1NumericUnknownReference GrammarV1StaticReference
  | GrammarV1NumericUnsupportedExpression GrammarV1Expression
  | GrammarV1NumericNegationUnsupported NumericType
  | GrammarV1NumericConversionTargetRequired
  | GrammarV1NumericConversionError NumericConversionError
  | GrammarV1NumericMixedDomainRequiresConversion NumericType NumericType
  | GrammarV1NumericArithmeticOutOfRange NumericType Integer
  | GrammarV1NumericDivideByZero NumericType IntegerDivisionOperator
  | GrammarV1NumericUnsupportedOperator NumericType GrammarV1BinaryOperator
  | GrammarV1NumericFloatError FloatSemanticError
  | GrammarV1NumericShiftOperandIntegerRequired NumericType
  | GrammarV1NumericShiftCountIntegerRequired NumericType
  | GrammarV1NumericShiftError IntegerShiftError
  deriving (Eq, Show)

-- | Evaluate the bounded numeric expression fragment after parsing. Every leaf in
-- the environment already has exact semantic numeric identity. Binary operators
-- require identical domains; crossing width/signedness/integer-float boundaries
-- is possible only through an explicit GrammarV1ConvertExpression node. Shifts
-- preserve the left operand's integer domain and delegate all count/range meaning
-- to EXEC-021's exact Core shift authority.
evaluateGrammarV1NumericExpression
  :: GrammarV1NumericEnvironment
  -> GrammarV1Expression
  -> Either GrammarV1NumericEvaluationError NumericValue
evaluateGrammarV1NumericExpression environment = evaluate
  where
    evaluate expression = case expression of
      GrammarV1NameExpression reference arguments
        | null arguments -> case Map.lookup reference environment of
            Just value -> Right value
            Nothing -> Left (GrammarV1NumericUnknownReference reference)
        | otherwise -> Left (GrammarV1NumericUnsupportedExpression expression)
      GrammarV1ParenthesizedExpression (Located _ inner) -> evaluate inner
      GrammarV1NegateExpression (Located _ inner) -> evaluate inner >>= applyNegation
      GrammarV1ConvertExpression value targetSource -> do
        sourceValue <- evaluate (locatedValue value)
        target <- case grammarV1PrimitiveType (locatedValue targetSource)
            >>= numericTypeFromCoreType of
          Just numericTarget -> Right numericTarget
          Nothing -> Left GrammarV1NumericConversionTargetRequired
        result <- mapLeft GrammarV1NumericConversionError
          (convertNumericValue target sourceValue)
        Right (numericConversionValue result)
      GrammarV1ShiftExpression left operator right -> do
        leftValue <- evaluate (locatedValue left)
        rightValue <- evaluate (locatedValue right)
        applyShift (locatedValue operator) leftValue rightValue
      GrammarV1BinaryExpression left operator right -> do
        leftValue <- evaluate (locatedValue left)
        rightValue <- evaluate (locatedValue right)
        applyBinary (locatedValue operator) leftValue rightValue
      _ -> Left (GrammarV1NumericUnsupportedExpression expression)

applyNegation
  :: NumericValue
  -> Either GrammarV1NumericEvaluationError NumericValue
applyNegation value = case value of
  NumericUIntValue width _ ->
    Left (GrammarV1NumericNegationUnsupported (NumericUIntType width))
  NumericSIntValue literal ->
    let result = SIntLiteral (sIntLiteralType literal) (negate (sIntLiteralValue literal))
    in if sIntLiteralInRange result
        then Right (NumericSIntValue result)
        else Left (GrammarV1NumericArithmeticOutOfRange
          (NumericSIntType (sIntLiteralType literal))
          (sIntLiteralValue result))
  NumericFloatValue floatValue ->
    Right (NumericFloatValue (negateFloatValue floatValue))

applyShift
  :: GrammarV1ShiftOperator
  -> NumericValue
  -> NumericValue
  -> Either GrammarV1NumericEvaluationError NumericValue
applyShift sourceOperator value countValue = do
  count <- integerShiftCount countValue
  let operator = case sourceOperator of
        GrammarV1ShiftLeft -> IntegerShiftLeft
        GrammarV1ShiftRight -> IntegerShiftRight
  case value of
    NumericUIntValue width integerValue ->
      NumericUIntValue width <$> mapLeft GrammarV1NumericShiftError
        (applyUIntShift operator width integerValue count)
    NumericSIntValue literal -> do
      result <- mapLeft GrammarV1NumericShiftError
        (applySIntShift operator (sIntLiteralType literal)
          (sIntLiteralValue literal) count)
      Right (NumericSIntValue (SIntLiteral (sIntLiteralType literal) result))
    NumericFloatValue floatValue ->
      Left (GrammarV1NumericShiftOperandIntegerRequired
        (NumericFloatType (floatFormat floatValue)))

integerShiftCount
  :: NumericValue
  -> Either GrammarV1NumericEvaluationError Integer
integerShiftCount value = case value of
  NumericUIntValue _ count -> Right count
  NumericSIntValue literal -> Right (sIntLiteralValue literal)
  NumericFloatValue floatValue ->
    Left (GrammarV1NumericShiftCountIntegerRequired
      (NumericFloatType (floatFormat floatValue)))

applyBinary
  :: GrammarV1BinaryOperator
  -> NumericValue
  -> NumericValue
  -> Either GrammarV1NumericEvaluationError NumericValue
applyBinary operator left right = case (left, right) of
  (NumericUIntValue leftWidth leftValue, NumericUIntValue rightWidth rightValue)
    | leftWidth == rightWidth ->
        applyUInt operator leftWidth leftValue rightValue
  (NumericSIntValue leftLiteral, NumericSIntValue rightLiteral)
    | sIntLiteralType leftLiteral == sIntLiteralType rightLiteral ->
        applySInt operator (sIntLiteralType leftLiteral)
          (sIntLiteralValue leftLiteral) (sIntLiteralValue rightLiteral)
  (NumericFloatValue leftValue, NumericFloatValue rightValue)
    | floatFormat leftValue == floatFormat rightValue ->
        applyFloat operator leftValue rightValue
  _ -> Left (GrammarV1NumericMixedDomainRequiresConversion
    (numericValueType left) (numericValueType right))

applyUInt
  :: GrammarV1BinaryOperator
  -> Int
  -> Integer
  -> Integer
  -> Either GrammarV1NumericEvaluationError NumericValue
applyUInt operator width left right = case operator of
  GrammarV1Add -> exact (left + right)
  GrammarV1Subtract -> exact (left - right)
  GrammarV1Multiply -> exact (left * right)
  GrammarV1Divide
    | right == 0 -> divideByZero IntegerQuotient
    | otherwise -> exact (left `div` right)
  GrammarV1Remainder
    | right == 0 -> divideByZero IntegerRemainder
    | otherwise -> exact (left `mod` right)
  where
    target = NumericUIntType width
    exact result
      | width > 0 && result >= 0 && result < 2 ^ width =
          Right (NumericUIntValue width result)
      | otherwise = Left (GrammarV1NumericArithmeticOutOfRange target result)
    divideByZero divisionOperator =
      Left (GrammarV1NumericDivideByZero target divisionOperator)

applySInt
  :: GrammarV1BinaryOperator
  -> SIntType
  -> Integer
  -> Integer
  -> Either GrammarV1NumericEvaluationError NumericValue
applySInt operator signedType left right = case operator of
  GrammarV1Add -> exact (applySIntArithmeticOperator SIntAdd left right)
  GrammarV1Subtract -> exact (applySIntArithmeticOperator SIntSubtract left right)
  GrammarV1Multiply -> exact (applySIntArithmeticOperator SIntMultiply left right)
  GrammarV1Divide
    | right == 0 -> divideByZero IntegerQuotient
    | otherwise -> exact (fst (signedQuotientRemainder left right))
  GrammarV1Remainder
    | right == 0 -> divideByZero IntegerRemainder
    | otherwise -> exact (snd (signedQuotientRemainder left right))
  where
    target = NumericSIntType signedType
    exact result =
      let literal = SIntLiteral signedType result
      in if sIntLiteralInRange literal
          then Right (NumericSIntValue literal)
          else Left (GrammarV1NumericArithmeticOutOfRange target result)
    divideByZero divisionOperator =
      Left (GrammarV1NumericDivideByZero target divisionOperator)

applyFloat
  :: GrammarV1BinaryOperator
  -> FloatValue
  -> FloatValue
  -> Either GrammarV1NumericEvaluationError NumericValue
applyFloat operator left right = do
  coreOperator <- case operator of
    GrammarV1Add -> Right FloatAdd
    GrammarV1Subtract -> Right FloatSubtract
    GrammarV1Multiply -> Right FloatMultiply
    GrammarV1Divide -> Right FloatDivide
    GrammarV1Remainder -> Left
      (GrammarV1NumericUnsupportedOperator
        (NumericFloatType (floatFormat left)) GrammarV1Remainder)
  NumericFloatValue <$> mapLeft GrammarV1NumericFloatError
    (applyFloatOperator coreOperator left right)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
