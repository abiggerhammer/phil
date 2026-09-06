{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.FloatArithmetic
  ( FloatFormat (..)
  , FloatValue
  , FloatClass (..)
  , FloatOperator (..)
  , FloatComparison (..)
  , FloatSemanticError (..)
  , FloatRoundingMode (..)
  , FloatRealizationWeakening (..)
  , FloatRealizationProfile (..)
  , CheckedFloatRealization
  , FloatRealizationError (..)
  , floatFormat
  , floatBits
  , floatFromBits
  , floatCoreType
  , floatTypeFromCoreType
  , floatDecimalLiteral
  , classifyFloat
  , applyFloatOperator
  , negateFloatValue
  , compareFloatValues
  , positiveZero
  , negativeZero
  , positiveInfinity
  , negativeInfinity
  , canonicalNaN
  , strictFloatRealizationProfile
  , checkFloatRealizationProfile
  ) where

import Data.Bits
  ( (.&.)
  , (.|.)
  , shiftL
  , shiftR
  , xor
  )
import Data.Ratio
  ( denominator
  , numerator
  , (%)
  )
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Read as TextRead
import Data.Word (Word64)
import Phil.Core.Syntax
  ( RefSort (..)
  , Ty (..)
  )

-- | EXEC-018 owns strict floating semantic identity independently of host and
-- backend floating carriers. A FloatValue is the exact IEEE interchange bit
-- pattern for its declared format; no Haskell Float/Double value is semantic
-- authority for parsing, arithmetic, comparison, or realization checking.
data FloatFormat
  = Float32
  | Float64
  deriving (Eq, Ord, Show)

data FloatValue = FloatValue
  { floatFormat :: FloatFormat
  , floatBits :: Word64
  }
  deriving (Eq, Ord, Show)

data FloatClass
  = FloatFinite Rational
  | FloatPositiveZero
  | FloatNegativeZero
  | FloatPositiveInfinity
  | FloatNegativeInfinity
  | FloatNaN Word64
  deriving (Eq, Show)

data FloatOperator
  = FloatAdd
  | FloatSubtract
  | FloatMultiply
  | FloatDivide
  deriving (Eq, Ord, Show)

data FloatComparison
  = FloatLess
  | FloatEqual
  | FloatGreater
  | FloatUnordered
  deriving (Eq, Ord, Show)

data FloatSemanticError
  = FloatBitsOutOfRange FloatFormat Word64
  | FloatLiteralMalformed Text
  | FloatFormatMismatch FloatFormat FloatFormat
  deriving (Eq, Show)

-- | The source contract fixes round-to-nearest, ties-to-even. Other rounding
-- modes may exist in a target, but they do not realize ordinary Phil floating
-- arithmetic without a separately admitted semantic relation.
data FloatRoundingMode
  = FloatRoundNearestTiesToEven
  | FloatOtherRounding Text
  deriving (Eq, Ord, Show)

-- | Target switches commonly grouped under "fast math" are named separately so
-- no backend can hide a semantic weakening behind one opaque optimization bit.
data FloatRealizationWeakening
  = FloatReassociation
  | FloatContraction
  | FloatAssumeNoNaN
  | FloatAssumeNoInfinity
  | FloatIgnoreSignedZero
  | FloatFlushToZero
  | FloatApproximateArithmetic
  deriving (Eq, Ord, Show)

data FloatRealizationProfile = FloatRealizationProfile
  { floatRealizationFormat :: FloatFormat
  , floatRealizationStorageBits :: Int
  , floatRealizationRoundingMode :: FloatRoundingMode
  , floatRealizationGradualUnderflow :: Bool
  , floatRealizationWeakenings :: Set.Set FloatRealizationWeakening
  }
  deriving (Eq, Show)

newtype CheckedFloatRealization = CheckedFloatRealization FloatRealizationProfile
  deriving (Eq, Show)

data FloatRealizationError
  = FloatRealizationWidthMismatch FloatFormat Int Int
  | FloatRealizationRoundingMismatch FloatRoundingMode
  | FloatRealizationFlushesSubnormals
  | FloatRealizationSemanticWeakening (Set.Set FloatRealizationWeakening)
  deriving (Eq, Show)

floatFromBits :: FloatFormat -> Word64 -> Either FloatSemanticError FloatValue
floatFromBits format bits
  | bits .&. complementMask format == 0 = Right (FloatValue format bits)
  | otherwise = Left (FloatBitsOutOfRange format bits)

floatCoreType :: FloatFormat -> Ty
floatCoreType format =
  TyOpaqueSorted (renderFormat format) (SortOpaque ("phil.float.v1:" <> renderFormat format))

floatTypeFromCoreType :: Ty -> Maybe FloatFormat
floatTypeFromCoreType ty = case ty of
  TyOpaqueSorted display (SortOpaque semantic)
    | display == "F32"
    , semantic == "phil.float.v1:F32" -> Just Float32
    | display == "F64"
    , semantic == "phil.float.v1:F64" -> Just Float64
  _ -> Nothing

-- | Parse the exact Grammar-v1 digits.digits literal language, with an optional
-- sign supplied by the unary-minus source route, then round the exact decimal
-- rational directly to the declared format using ties-to-even.
floatDecimalLiteral
  :: FloatFormat
  -> Text
  -> Either FloatSemanticError FloatValue
floatDecimalLiteral format text = do
  let (negative, unsigned) = case Text.stripPrefix "-" text of
        Just rest -> (True, rest)
        Nothing -> (False, text)
  (whole, fractional) <- case Text.splitOn "." unsigned of
    [wholeDigits, fractionalDigits]
      | not (Text.null wholeDigits)
      , not (Text.null fractionalDigits)
      , Text.all asciiDigit wholeDigits
      , Text.all asciiDigit fractionalDigits -> Right (wholeDigits, fractionalDigits)
    _ -> Left (FloatLiteralMalformed text)
  wholeValue <- decimalInteger whole text
  fractionalValue <- decimalInteger fractional text
  let scale = 10 ^ Text.length fractional
      magnitude = (wholeValue * scale + fractionalValue) % scale
      signedValue = if negative then negate magnitude else magnitude
  Right (roundFinite format signedValue (negative && magnitude == 0))

classifyFloat :: FloatValue -> FloatClass
classifyFloat value@(FloatValue format bits) =
  let parameters = formatParameters format
      sign = signBitSet parameters bits
      exponent = exponentField parameters bits
      fraction = fractionField parameters bits
      allOnes = exponentMaskValue parameters
  in if exponent == allOnes
      then if fraction == 0
        then if sign then FloatNegativeInfinity else FloatPositiveInfinity
        else FloatNaN bits
      else if exponent == 0 && fraction == 0
        then if sign then FloatNegativeZero else FloatPositiveZero
        else FloatFinite (finiteRational value)

applyFloatOperator
  :: FloatOperator
  -> FloatValue
  -> FloatValue
  -> Either FloatSemanticError FloatValue
applyFloatOperator operator left right = do
  ensureSameFormat left right
  Right $ case operator of
    FloatAdd -> addValues left right
    FloatSubtract -> addValues left (negateFloatValue right)
    FloatMultiply -> multiplyValues left right
    FloatDivide -> divideValues left right

negateFloatValue :: FloatValue -> FloatValue
negateFloatValue (FloatValue format bits) =
  let parameters = formatParameters format
  in FloatValue format (bits `xor` signMask parameters)

compareFloatValues
  :: FloatValue
  -> FloatValue
  -> Either FloatSemanticError FloatComparison
compareFloatValues left right = do
  ensureSameFormat left right
  Right $ case (decode left, decode right) of
    (DecodedNaN, _) -> FloatUnordered
    (_, DecodedNaN) -> FloatUnordered
    (DecodedInfinity leftNegative, DecodedInfinity rightNegative)
      | leftNegative == rightNegative -> FloatEqual
      | leftNegative -> FloatLess
      | otherwise -> FloatGreater
    (DecodedInfinity leftNegative, DecodedFinite {}) ->
      if leftNegative then FloatLess else FloatGreater
    (DecodedFinite {}, DecodedInfinity rightNegative) ->
      if rightNegative then FloatGreater else FloatLess
    (DecodedFinite leftNegative leftMagnitude, DecodedFinite rightNegative rightMagnitude) ->
      compareFinite
        (signedRational leftNegative leftMagnitude)
        (signedRational rightNegative rightMagnitude)

positiveZero :: FloatFormat -> FloatValue
positiveZero format = FloatValue format 0

negativeZero :: FloatFormat -> FloatValue
negativeZero format = FloatValue format (signMask (formatParameters format))

positiveInfinity :: FloatFormat -> FloatValue
positiveInfinity format =
  let parameters = formatParameters format
  in FloatValue format (exponentMaskBits parameters)

negativeInfinity :: FloatFormat -> FloatValue
negativeInfinity format =
  let parameters = formatParameters format
  in FloatValue format (signMask parameters .|. exponentMaskBits parameters)

canonicalNaN :: FloatFormat -> FloatValue
canonicalNaN format =
  let parameters = formatParameters format
      quietBit = 1 `shiftL` (fractionBitCount parameters - 1)
  in FloatValue format (exponentMaskBits parameters .|. quietBit)

strictFloatRealizationProfile :: FloatFormat -> FloatRealizationProfile
strictFloatRealizationProfile format = FloatRealizationProfile
  { floatRealizationFormat = format
  , floatRealizationStorageBits = totalBitCount (formatParameters format)
  , floatRealizationRoundingMode = FloatRoundNearestTiesToEven
  , floatRealizationGradualUnderflow = True
  , floatRealizationWeakenings = Set.empty
  }

checkFloatRealizationProfile
  :: FloatRealizationProfile
  -> Either FloatRealizationError CheckedFloatRealization
checkFloatRealizationProfile profile = do
  let expectedWidth = totalBitCount (formatParameters (floatRealizationFormat profile))
  if floatRealizationStorageBits profile == expectedWidth
    then Right ()
    else Left (FloatRealizationWidthMismatch
      (floatRealizationFormat profile)
      expectedWidth
      (floatRealizationStorageBits profile))
  case floatRealizationRoundingMode profile of
    FloatRoundNearestTiesToEven -> Right ()
    other -> Left (FloatRealizationRoundingMismatch other)
  if floatRealizationGradualUnderflow profile
    then Right ()
    else Left FloatRealizationFlushesSubnormals
  if Set.null (floatRealizationWeakenings profile)
    then Right (CheckedFloatRealization profile)
    else Left (FloatRealizationSemanticWeakening (floatRealizationWeakenings profile))

-- Internal exact IEEE model --------------------------------------------------

data FormatParameters = FormatParameters
  { totalBitCount :: Int
  , exponentBitCount :: Int
  , fractionBitCount :: Int
  , exponentBias :: Int
  }

formatParameters :: FloatFormat -> FormatParameters
formatParameters format = case format of
  Float32 -> FormatParameters 32 8 23 127
  Float64 -> FormatParameters 64 11 52 1023

renderFormat :: FloatFormat -> Text
renderFormat format = case format of
  Float32 -> "F32"
  Float64 -> "F64"

signMask :: FormatParameters -> Word64
signMask parameters = 1 `shiftL` (totalBitCount parameters - 1)

complementMask :: FloatFormat -> Word64
complementMask format =
  let bits = totalBitCount (formatParameters format)
  in if bits == 64 then 0 else complementLowBits bits

complementLowBits :: Int -> Word64
complementLowBits bits = complement (lowBitsMask bits)

lowBitsMask :: Int -> Word64
lowBitsMask bits
  | bits >= 64 = maxBound
  | otherwise = (1 `shiftL` bits) - 1

exponentMaskValue :: FormatParameters -> Word64
exponentMaskValue parameters = lowBitsMask (exponentBitCount parameters)

fractionMask :: FormatParameters -> Word64
fractionMask parameters = lowBitsMask (fractionBitCount parameters)

exponentMaskBits :: FormatParameters -> Word64
exponentMaskBits parameters =
  exponentMaskValue parameters `shiftL` fractionBitCount parameters

signBitSet :: FormatParameters -> Word64 -> Bool
signBitSet parameters bits = bits .&. signMask parameters /= 0

exponentField :: FormatParameters -> Word64 -> Word64
exponentField parameters bits =
  (bits `shiftR` fractionBitCount parameters) .&. exponentMaskValue parameters

fractionField :: FormatParameters -> Word64 -> Word64
fractionField parameters bits = bits .&. fractionMask parameters

finiteRational :: FloatValue -> Rational
finiteRational (FloatValue format bits) =
  let parameters = formatParameters format
      negative = signBitSet parameters bits
      exponent = toInteger (exponentField parameters bits)
      fraction = toInteger (fractionField parameters bits)
      fractionBits = fractionBitCount parameters
      bias = exponentBias parameters
      magnitude
        | exponent == 0 =
            fromInteger fraction * powerOfTwoRational (1 - bias - fractionBits)
        | otherwise =
            fromInteger ((2 ^ fractionBits) + fraction)
              * powerOfTwoRational (fromInteger exponent - bias - fractionBits)
  in if negative then negate magnitude else magnitude

data DecodedFloat
  = DecodedNaN
  | DecodedInfinity Bool
  | DecodedFinite Bool Rational

decode :: FloatValue -> DecodedFloat
decode value = case classifyFloat value of
  FloatNaN _ -> DecodedNaN
  FloatPositiveInfinity -> DecodedInfinity False
  FloatNegativeInfinity -> DecodedInfinity True
  FloatPositiveZero -> DecodedFinite False 0
  FloatNegativeZero -> DecodedFinite True 0
  FloatFinite rational -> DecodedFinite (rational < 0) (abs rational)

addValues :: FloatValue -> FloatValue -> FloatValue
addValues left right =
  let format = floatFormat left
  in case (decode left, decode right) of
      (DecodedNaN, _) -> canonicalNaN format
      (_, DecodedNaN) -> canonicalNaN format
      (DecodedInfinity leftNegative, DecodedInfinity rightNegative)
        | leftNegative /= rightNegative -> canonicalNaN format
        | leftNegative -> negativeInfinity format
        | otherwise -> positiveInfinity format
      (DecodedInfinity negative, _) ->
        if negative then negativeInfinity format else positiveInfinity format
      (_, DecodedInfinity negative) ->
        if negative then negativeInfinity format else positiveInfinity format
      (DecodedFinite leftNegative leftMagnitude, DecodedFinite rightNegative rightMagnitude) ->
        let exact =
              signedRational leftNegative leftMagnitude
                + signedRational rightNegative rightMagnitude
            negativeExactZero =
              leftMagnitude == 0
                && rightMagnitude == 0
                && leftNegative
                && rightNegative
        in roundFinite format exact negativeExactZero

multiplyValues :: FloatValue -> FloatValue -> FloatValue
multiplyValues left right =
  let format = floatFormat left
  in case (decode left, decode right) of
      (DecodedNaN, _) -> canonicalNaN format
      (_, DecodedNaN) -> canonicalNaN format
      (DecodedInfinity leftNegative, DecodedFinite rightNegative rightMagnitude)
        | rightMagnitude == 0 -> canonicalNaN format
        | otherwise -> infinityWithSign format (leftNegative /= rightNegative)
      (DecodedFinite leftNegative leftMagnitude, DecodedInfinity rightNegative)
        | leftMagnitude == 0 -> canonicalNaN format
        | otherwise -> infinityWithSign format (leftNegative /= rightNegative)
      (DecodedInfinity leftNegative, DecodedInfinity rightNegative) ->
        infinityWithSign format (leftNegative /= rightNegative)
      (DecodedFinite leftNegative leftMagnitude, DecodedFinite rightNegative rightMagnitude) ->
        let negative = leftNegative /= rightNegative
            exact = signedRational negative (leftMagnitude * rightMagnitude)
        in roundFinite format exact (negative && (leftMagnitude == 0 || rightMagnitude == 0))

divideValues :: FloatValue -> FloatValue -> FloatValue
divideValues left right =
  let format = floatFormat left
  in case (decode left, decode right) of
      (DecodedNaN, _) -> canonicalNaN format
      (_, DecodedNaN) -> canonicalNaN format
      (DecodedInfinity {}, DecodedInfinity {}) -> canonicalNaN format
      (DecodedFinite _ leftMagnitude, DecodedFinite _ rightMagnitude)
        | leftMagnitude == 0 && rightMagnitude == 0 -> canonicalNaN format
      (DecodedInfinity leftNegative, DecodedFinite rightNegative _) ->
        infinityWithSign format (leftNegative /= rightNegative)
      (DecodedFinite leftNegative _, DecodedInfinity rightNegative) ->
        zeroWithSign format (leftNegative /= rightNegative)
      (DecodedFinite leftNegative leftMagnitude, DecodedFinite rightNegative rightMagnitude)
        | rightMagnitude == 0 -> infinityWithSign format (leftNegative /= rightNegative)
        | leftMagnitude == 0 -> zeroWithSign format (leftNegative /= rightNegative)
        | otherwise ->
            let negative = leftNegative /= rightNegative
                exact = signedRational negative (leftMagnitude / rightMagnitude)
            in roundFinite format exact False

infinityWithSign :: FloatFormat -> Bool -> FloatValue
infinityWithSign format negative =
  if negative then negativeInfinity format else positiveInfinity format

zeroWithSign :: FloatFormat -> Bool -> FloatValue
zeroWithSign format negative =
  if negative then negativeZero format else positiveZero format

signedRational :: Bool -> Rational -> Rational
signedRational negative magnitude =
  if negative then negate magnitude else magnitude

compareFinite :: Rational -> Rational -> FloatComparison
compareFinite left right = case compare left right of
  LT -> FloatLess
  EQ -> FloatEqual
  GT -> FloatGreater

ensureSameFormat :: FloatValue -> FloatValue -> Either FloatSemanticError ()
ensureSameFormat left right
  | floatFormat left == floatFormat right = Right ()
  | otherwise = Left (FloatFormatMismatch (floatFormat left) (floatFormat right))

roundFinite :: FloatFormat -> Rational -> Bool -> FloatValue
roundFinite format value negativeExactZero
  | value == 0 = zeroWithSign format negativeExactZero
  | otherwise =
      let parameters = formatParameters format
          negative = value < 0
          magnitude = abs value
          exponent = floorLog2Rational magnitude
          minimumNormalExponent = 1 - exponentBias parameters
      in if exponent < minimumNormalExponent
          then roundSubnormal parameters format negative magnitude
          else roundNormal parameters format negative magnitude exponent

roundNormal
  :: FormatParameters
  -> FloatFormat
  -> Bool
  -> Rational
  -> Int
  -> FloatValue
roundNormal parameters format negative magnitude exponent =
  let fractionBits = fractionBitCount parameters
      maximumExponent = exponentBias parameters
      scaled = scaleByPowerOfTwo magnitude (fractionBits - exponent)
      significand = roundNearestEven scaled
      carry = significand >= 2 ^ (fractionBits + 1)
      finalExponent = if carry then exponent + 1 else exponent
      finalSignificand = if carry then 2 ^ fractionBits else significand
  in if finalExponent > maximumExponent
      then infinityWithSign format negative
      else
        let exponentBits = toWord64 (finalExponent + exponentBias parameters)
            fractionBitsValue = toWord64 (finalSignificand - 2 ^ fractionBits)
            raw = signBits parameters negative
              .|. (exponentBits `shiftL` fractionBits)
              .|. fractionBitsValue
        in FloatValue format raw

roundSubnormal
  :: FormatParameters
  -> FloatFormat
  -> Bool
  -> Rational
  -> FloatValue
roundSubnormal parameters format negative magnitude =
  let fractionBits = fractionBitCount parameters
      scaled = scaleByPowerOfTwo
        magnitude
        (fractionBits + exponentBias parameters - 1)
      fraction = roundNearestEven scaled
  in if fraction == 0
      then zeroWithSign format negative
      else if fraction >= 2 ^ fractionBits
        then FloatValue format
          (signBits parameters negative .|. (1 `shiftL` fractionBits))
        else FloatValue format
          (signBits parameters negative .|. toWord64 fraction)

roundNearestEven :: Rational -> Integer
roundNearestEven value =
  let n = numerator value
      d = denominator value
      (quotient, remainder) = n `quotRem` d
  in case compare (2 * remainder) d of
      LT -> quotient
      GT -> quotient + 1
      EQ -> if even quotient then quotient else quotient + 1

floorLog2Rational :: Rational -> Int
floorLog2Rational value =
  let n = numerator value
      d = denominator value
      initial = integerLog2 n - integerLog2 d
  in if value < powerOfTwoRational initial
      then initial - 1
      else if value >= powerOfTwoRational (initial + 1)
        then initial + 1
        else initial

integerLog2 :: Integer -> Int
integerLog2 value
  | value <= 0 = error "integerLog2: nonpositive input"
  | otherwise = go 0 value
  where
    go result current
      | current < 2 = result
      | otherwise = go (result + 1) (current `quot` 2)

powerOfTwoRational :: Int -> Rational
powerOfTwoRational exponent
  | exponent >= 0 = fromInteger (2 ^ exponent)
  | otherwise = 1 % (2 ^ negate exponent)

scaleByPowerOfTwo :: Rational -> Int -> Rational
scaleByPowerOfTwo value exponent = value * powerOfTwoRational exponent

signBits :: FormatParameters -> Bool -> Word64
signBits parameters negative = if negative then signMask parameters else 0

toWord64 :: Integer -> Word64
toWord64 = fromInteger

decimalInteger :: Text -> Text -> Either FloatSemanticError Integer
decimalInteger digits original =
  case TextRead.decimal digits :: Either String (Integer, Text) of
    Right (value, rest)
      | Text.null rest -> Right value
    _ -> Left (FloatLiteralMalformed original)

asciiDigit :: Char -> Bool
asciiDigit character = character >= '0' && character <= '9'
