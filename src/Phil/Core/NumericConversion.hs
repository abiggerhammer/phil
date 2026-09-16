{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.NumericConversion
  ( NumericType (..)
  , NumericValue (..)
  , NumericConversionPrecision (..)
  , NumericConversionResult (..)
  , NumericConversionError (..)
  , CheckedNumericConversion (..)
  , numericTypeFromCoreType
  , numericValueType
  , convertNumericValue
  , checkedConvertNumericValue
  ) where

import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.FloatArithmetic
  ( FloatClass (..)
  , FloatFormat
  , FloatSemanticError
  , FloatValue
  , canonicalNaN
  , classifyFloat
  , floatDecimalLiteral
  , floatFormat
  , floatTypeFromCoreType
  , negativeInfinity
  , negativeZero
  , positiveInfinity
  , positiveZero
  )
import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntType (..)
  , sIntLiteralInRange
  , sIntTypeFromCoreType
  )
import Phil.Core.Syntax (Ty (..))

-- | EXEC-020 keeps numeric-domain identity explicit. There is deliberately no
-- generic machine-number carrier whose host representation could choose a cast.
data NumericType
  = NumericUIntType Int
  | NumericSIntType SIntType
  | NumericFloatType FloatFormat
  deriving (Eq, Ord, Show)

data NumericValue
  = NumericUIntValue Int Integer
  | NumericSIntValue SIntLiteral
  | NumericFloatValue FloatValue
  deriving (Eq, Show)

data NumericConversionPrecision
  = NumericConversionExact
  | NumericConversionRounded
  | NumericConversionNaNCanonicalized
  deriving (Eq, Ord, Show)

data NumericConversionResult = NumericConversionResult
  { numericConversionValue :: NumericValue
  , numericConversionPrecision :: NumericConversionPrecision
  }
  deriving (Eq, Show)

data NumericConversionError
  = NumericConversionInvalidTarget NumericType
  | NumericConversionInvalidSource NumericValue
  | NumericConversionOutOfRange NumericType NumericValue
  | NumericConversionFractional NumericType Rational
  | NumericConversionNonFinite NumericType FloatClass
  | NumericConversionExactDecimalUnavailable Rational
  | NumericConversionFloatError FloatSemanticError
  deriving (Eq, Show)

data CheckedNumericConversion
  = CheckedNumericConversionSucceeded NumericConversionResult
  | CheckedNumericConversionFailed NumericConversionError
  deriving (Eq, Show)

numericTypeFromCoreType :: Ty -> Maybe NumericType
numericTypeFromCoreType ty = case ty of
  TyUInt width
    | width > 0 -> Just (NumericUIntType width)
  _ -> case sIntTypeFromCoreType ty of
    Just signedType -> Just (NumericSIntType signedType)
    Nothing -> NumericFloatType <$> floatTypeFromCoreType ty

numericValueType :: NumericValue -> NumericType
numericValueType value = case value of
  NumericUIntValue width _ -> NumericUIntType width
  NumericSIntValue literal -> NumericSIntType (sIntLiteralType literal)
  NumericFloatValue floatValue -> NumericFloatType (floatFormat floatValue)

-- | Execute one explicit semantic conversion. Plain callers get an exact
-- rejection on partial failure; checked callers can expose the same rejection as
-- an explicit typed-negative outcome via 'checkedConvertNumericValue'.
convertNumericValue
  :: NumericType
  -> NumericValue
  -> Either NumericConversionError NumericConversionResult
convertNumericValue target source = do
  validateTarget target
  validateSource source
  case target of
    NumericUIntType width -> convertToUInt width source
    NumericSIntType signedType -> convertToSInt signedType source
    NumericFloatType format -> convertToFloat format source

checkedConvertNumericValue :: NumericType -> NumericValue -> CheckedNumericConversion
checkedConvertNumericValue target source =
  case convertNumericValue target source of
    Right result -> CheckedNumericConversionSucceeded result
    Left conversionError -> CheckedNumericConversionFailed conversionError

convertToUInt
  :: Int
  -> NumericValue
  -> Either NumericConversionError NumericConversionResult
convertToUInt width source = do
  value <- exactIntegerSource (NumericUIntType width) source
  if fitsUInt width value
    then Right NumericConversionResult
      { numericConversionValue = NumericUIntValue width value
      , numericConversionPrecision = NumericConversionExact
      }
    else Left (NumericConversionOutOfRange (NumericUIntType width) source)

convertToSInt
  :: SIntType
  -> NumericValue
  -> Either NumericConversionError NumericConversionResult
convertToSInt signedType source = do
  value <- exactIntegerSource (NumericSIntType signedType) source
  let literal = SIntLiteral signedType value
  if sIntLiteralInRange literal
    then Right NumericConversionResult
      { numericConversionValue = NumericSIntValue literal
      , numericConversionPrecision = NumericConversionExact
      }
    else Left (NumericConversionOutOfRange (NumericSIntType signedType) source)

convertToFloat
  :: FloatFormat
  -> NumericValue
  -> Either NumericConversionError NumericConversionResult
convertToFloat targetFormat source = case source of
  NumericFloatValue value
    | floatFormat value == targetFormat -> Right NumericConversionResult
        { numericConversionValue = source
        , numericConversionPrecision = NumericConversionExact
        }
    | otherwise -> convertFloatClass targetFormat source (classifyFloat value)
  NumericUIntValue _ value -> convertFiniteToFloat targetFormat source (fromInteger value)
  NumericSIntValue literal ->
    convertFiniteToFloat targetFormat source (fromInteger (sIntLiteralValue literal))

convertFloatClass
  :: FloatFormat
  -> NumericValue
  -> FloatClass
  -> Either NumericConversionError NumericConversionResult
convertFloatClass targetFormat source floatClass = case floatClass of
  FloatPositiveZero -> exactFloat (positiveZero targetFormat)
  FloatNegativeZero -> exactFloat (negativeZero targetFormat)
  FloatPositiveInfinity -> exactFloat (positiveInfinity targetFormat)
  FloatNegativeInfinity -> exactFloat (negativeInfinity targetFormat)
  FloatNaN _ -> Right NumericConversionResult
    { numericConversionValue = NumericFloatValue (canonicalNaN targetFormat)
    , numericConversionPrecision = NumericConversionNaNCanonicalized
    }
  FloatFinite value -> convertFiniteToFloat targetFormat source value
  where
    exactFloat value = Right NumericConversionResult
      { numericConversionValue = NumericFloatValue value
      , numericConversionPrecision = NumericConversionExact
      }

convertFiniteToFloat
  :: FloatFormat
  -> NumericValue
  -> Rational
  -> Either NumericConversionError NumericConversionResult
convertFiniteToFloat targetFormat source exactValue = do
  decimal <- maybe
    (Left (NumericConversionExactDecimalUnavailable exactValue))
    Right
    (renderExactBinaryDecimal exactValue)
  converted <- mapLeft NumericConversionFloatError
    (floatDecimalLiteral targetFormat decimal)
  precision <- case classifyFloat converted of
    FloatFinite roundedValue -> Right
      (if roundedValue == exactValue then NumericConversionExact else NumericConversionRounded)
    FloatPositiveZero -> Right
      (if exactValue == 0 then NumericConversionExact else NumericConversionRounded)
    FloatNegativeZero -> Right
      (if exactValue == 0 then NumericConversionExact else NumericConversionRounded)
    FloatPositiveInfinity ->
      Left (NumericConversionOutOfRange (NumericFloatType targetFormat) source)
    FloatNegativeInfinity ->
      Left (NumericConversionOutOfRange (NumericFloatType targetFormat) source)
    FloatNaN _ ->
      Left (NumericConversionOutOfRange (NumericFloatType targetFormat) source)
  Right NumericConversionResult
    { numericConversionValue = NumericFloatValue converted
    , numericConversionPrecision = precision
    }

exactIntegerSource
  :: NumericType
  -> NumericValue
  -> Either NumericConversionError Integer
exactIntegerSource target source = case source of
  NumericUIntValue _ value -> Right value
  NumericSIntValue literal -> Right (sIntLiteralValue literal)
  NumericFloatValue floatValue -> case classifyFloat floatValue of
    FloatPositiveZero -> Right 0
    FloatNegativeZero -> Right 0
    FloatFinite rational
      | denominator rational == 1 -> Right (numerator rational)
      | otherwise -> Left (NumericConversionFractional target rational)
    other -> Left (NumericConversionNonFinite target other)

validateTarget :: NumericType -> Either NumericConversionError ()
validateTarget target = case target of
  NumericUIntType width
    | width <= 0 -> Left (NumericConversionInvalidTarget target)
  NumericSIntType (SIntType width)
    | width <= 0 -> Left (NumericConversionInvalidTarget target)
  _ -> Right ()

validateSource :: NumericValue -> Either NumericConversionError ()
validateSource source = case source of
  NumericUIntValue width value
    | not (fitsUInt width value) -> Left (NumericConversionInvalidSource source)
  NumericSIntValue literal
    | not (sIntLiteralInRange literal) -> Left (NumericConversionInvalidSource source)
  _ -> Right ()

fitsUInt :: Int -> Integer -> Bool
fitsUInt width value = width > 0 && value >= 0 && value < 2 ^ width

-- | Every finite IEEE binary value has a denominator that is a power of two, so
-- it has a finite exact decimal spelling. Rendering that exact spelling lets the
-- existing EXEC-018 decimal-to-binary RNE authority perform cross-format and
-- integer-to-float rounding without introducing host Float/Double semantics.
renderExactBinaryDecimal :: Rational -> Maybe Text
renderExactBinaryDecimal value = do
  places <- powerOfTwoExponent (denominator value)
  let signedNumerator = numerator value
      magnitude = abs signedNumerator * 5 ^ places
      digits = show magnitude
      decimalMagnitude
        | places == 0 = digits <> ".0"
        | length digits <= places =
            "0." <> replicate (places - length digits) '0' <> digits
        | otherwise =
            let split = length digits - places
                (whole, fractional) = splitAt split digits
            in whole <> "." <> fractional
      prefix = if signedNumerator < 0 then "-" else ""
  Just (Text.pack (prefix <> decimalMagnitude))

powerOfTwoExponent :: Integer -> Maybe Int
powerOfTwoExponent value
  | value == 1 = Just 0
  | value > 1 && even value = (1 +) <$> powerOfTwoExponent (value `div` 2)
  | otherwise = Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
