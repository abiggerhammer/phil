module Phil.Core.IntegerShift
  ( IntegerShiftOperator (..)
  , IntegerShiftError (..)
  , applyUIntShift
  , applySIntShift
  ) where

import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntType (..)
  , sIntLiteralInRange
  )

data IntegerShiftOperator
  = IntegerShiftLeft
  | IntegerShiftRight
  deriving (Eq, Ord, Show)

data IntegerShiftError
  = IntegerShiftInvalidWidth Int
  | IntegerShiftCountOutOfRange Int Integer
  | IntegerShiftUIntOperandOutOfRange Int Integer
  | IntegerShiftSIntOperandOutOfRange SIntType Integer
  | IntegerShiftUIntLeftResultOutOfRange Int Integer
  | IntegerShiftSIntLeftResultOutOfRange SIntType Integer
  deriving (Eq, Show)

-- | EXEC-021 unsigned shifts are mathematical operations, never target shifts.
-- In particular, the count is not masked and left shift never discards bits.
applyUIntShift
  :: IntegerShiftOperator
  -> Int
  -> Integer
  -> Integer
  -> Either IntegerShiftError Integer
applyUIntShift operator width value count = do
  validateWidthAndCount width count
  if value >= 0 && value < 2 ^ width
    then Right ()
    else Left (IntegerShiftUIntOperandOutOfRange width value)
  case operator of
    IntegerShiftLeft ->
      let result = value * 2 ^ count
      in if result < 2 ^ width
          then Right result
          else Left (IntegerShiftUIntLeftResultOutOfRange width result)
    IntegerShiftRight -> Right (value `div` 2 ^ count)

-- | Signed right shift is arithmetic/sign-extending with exact floor semantics.
-- This is intentionally not the truncation-toward-zero semantics of signed '/'.
applySIntShift
  :: IntegerShiftOperator
  -> SIntType
  -> Integer
  -> Integer
  -> Either IntegerShiftError Integer
applySIntShift operator signedType@(SIntType width) value count = do
  validateWidthAndCount width count
  let source = SIntLiteral signedType value
  if sIntLiteralInRange source
    then Right ()
    else Left (IntegerShiftSIntOperandOutOfRange signedType value)
  case operator of
    IntegerShiftLeft ->
      let result = value * 2 ^ count
          literal = SIntLiteral signedType result
      in if sIntLiteralInRange literal
          then Right result
          else Left (IntegerShiftSIntLeftResultOutOfRange signedType result)
    IntegerShiftRight -> Right (value `div` 2 ^ count)

validateWidthAndCount :: Int -> Integer -> Either IntegerShiftError ()
validateWidthAndCount width count
  | width <= 0 = Left (IntegerShiftInvalidWidth width)
  | count < 0 || count >= toInteger width =
      Left (IntegerShiftCountOutOfRange width count)
  | otherwise = Right ()
