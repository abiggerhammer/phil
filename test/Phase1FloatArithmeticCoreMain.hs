{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.FloatArithmetic
  ( FloatClass (..)
  , FloatComparison (..)
  , FloatFormat (..)
  , FloatOperator (..)
  , FloatRealizationError (..)
  , FloatRealizationProfile (..)
  , FloatRealizationWeakening (..)
  , FloatRoundingMode (..)
  , FloatSemanticError (..)
  , FloatValue
  , applyFloatOperator
  , canonicalNaN
  , checkFloatRealizationProfile
  , classifyFloat
  , compareFloatValues
  , floatBits
  , floatCoreType
  , floatDecimalLiteral
  , floatFromBits
  , floatTypeFromCoreType
  , negativeInfinity
  , negativeZero
  , positiveInfinity
  , positiveZero
  , strictFloatRealizationProfile
  )
import Phil.Core.Syntax (Ty (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-018 F32/F64 semantic type identity is exact" typeIdentity
    , test "EXEC-018 decimal literals round to known IEEE values" decimalRounding
    , test "EXEC-018 ties round to nearest even" tiesToEven
    , test "EXEC-018 signed zero is semantic" signedZero
    , test "EXEC-018 finite arithmetic is exact before rounding" finiteArithmetic
    , test "EXEC-018 infinity and NaN cases are explicit" infinityAndNaN
    , test "EXEC-018 comparison preserves NaN and signed-zero rules" comparisonRules
    , test "EXEC-018 gradual underflow retains subnormals" gradualUnderflow
    , test "EXEC-018 underflow tie may round to signed zero" subnormalTie
    , test "EXEC-018 overflow yields declared infinity rather than target drift" overflowRule
    , test "EXEC-018 format mismatch rejects" formatMismatch
    , test "EXEC-018 strict realization profile is admitted" strictProfileAccepted
    , test "EXEC-018 fast-math weakenings reject explicitly" fastMathRejects
    , test "EXEC-018 wrong rounding and FTZ reject" targetModeRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

typeIdentity :: Either String ()
typeIdentity = do
  assert (floatTypeFromCoreType (floatCoreType Float32) == Just Float32)
    "F32 exact Core identity did not round-trip"
  assert (floatTypeFromCoreType (floatCoreType Float64) == Just Float64)
    "F64 exact Core identity did not round-trip"
  assert (floatCoreType Float32 /= floatCoreType Float64)
    "F32 and F64 collapsed to one type"
  assert (floatTypeFromCoreType (TyUInt 32) == Nothing)
    "F32 was inferred from a same-width integer carrier"
  case floatFromBits Float32 0x100000000 of
    Left (FloatBitsOutOfRange Float32 0x100000000) -> Right ()
    other -> Left ("F32 accepted high representation bits: " <> show other)

decimalRounding :: Either String ()
decimalRounding = do
  f32One <- mapLeft show (floatDecimalLiteral Float32 "1.0")
  f32Tenth <- mapLeft show (floatDecimalLiteral Float32 "0.1")
  f64Tenth <- mapLeft show (floatDecimalLiteral Float64 "0.1")
  assert (floatBits f32One == 0x3f800000)
    ("F32 1.0 bits changed: " <> show (floatBits f32One))
  assert (floatBits f32Tenth == 0x3dcccccd)
    ("F32 0.1 rounding changed: " <> show (floatBits f32Tenth))
  assert (floatBits f64Tenth == 0x3fb999999999999a)
    ("F64 0.1 rounding changed: " <> show (floatBits f64Tenth))

tiesToEven :: Either String ()
tiesToEven = do
  halfway <- mapLeft show $
    floatDecimalLiteral Float32 "1.000000059604644775390625"
  assert (floatBits halfway == 0x3f800000)
    ("half-ULP tie did not choose even F32 significand: " <> show (floatBits halfway))

signedZero :: Either String ()
signedZero = do
  negative <- mapLeft show (floatDecimalLiteral Float32 "-0.0")
  positive <- mapLeft show (floatDecimalLiteral Float32 "0.0")
  assert (negative == negativeZero Float32)
    "negative decimal zero lost its sign"
  assert (positive == positiveZero Float32)
    "positive decimal zero changed identity"
  minusThree <- mapLeft show (floatDecimalLiteral Float32 "-3.0")
  productValue <- mapLeft show (applyFloatOperator FloatMultiply positive minusThree)
  assert (productValue == negativeZero Float32)
    ("+0 * -3 did not produce -0: " <> show (classifyFloat productValue))

finiteArithmetic :: Either String ()
finiteArithmetic = do
  onePointFive <- mapLeft show (floatDecimalLiteral Float32 "1.5")
  twoPointTwoFive <- mapLeft show (floatDecimalLiteral Float32 "2.25")
  sumValue <- mapLeft show (applyFloatOperator FloatAdd onePointFive twoPointTwoFive)
  assert (floatBits sumValue == 0x40700000)
    ("1.5 + 2.25 did not produce F32 3.75: " <> show (floatBits sumValue))
  seven <- mapLeft show (floatDecimalLiteral Float32 "7.0")
  two <- mapLeft show (floatDecimalLiteral Float32 "2.0")
  quotient <- mapLeft show (applyFloatOperator FloatDivide seven two)
  assert (floatBits quotient == 0x40600000)
    ("7.0 / 2.0 did not produce F32 3.5: " <> show (floatBits quotient))

infinityAndNaN :: Either String ()
infinityAndNaN = do
  invalidSum <- mapLeft show $
    applyFloatOperator FloatAdd (positiveInfinity Float32) (negativeInfinity Float32)
  assert (invalidSum == canonicalNaN Float32)
    ("+inf + -inf did not canonicalize NaN: " <> show (classifyFloat invalidSum))
  one <- mapLeft show (floatDecimalLiteral Float32 "1.0")
  divideByZero <- mapLeft show $
    applyFloatOperator FloatDivide one (positiveZero Float32)
  assert (divideByZero == positiveInfinity Float32)
    ("1.0 / +0 did not produce +inf: " <> show (classifyFloat divideByZero))
  zeroOverZero <- mapLeft show $
    applyFloatOperator FloatDivide (positiveZero Float32) (positiveZero Float32)
  assert (zeroOverZero == canonicalNaN Float32)
    ("0/0 did not produce canonical NaN: " <> show (classifyFloat zeroOverZero))

comparisonRules :: Either String ()
comparisonRules = do
  zeros <- mapLeft show $
    compareFloatValues (positiveZero Float64) (negativeZero Float64)
  assert (zeros == FloatEqual)
    "+0 and -0 were not numerically equal"
  unordered <- mapLeft show $
    compareFloatValues (canonicalNaN Float64) (positiveZero Float64)
  assert (unordered == FloatUnordered)
    "NaN comparison did not remain unordered"
  order <- mapLeft show $
    compareFloatValues (negativeInfinity Float64) (positiveInfinity Float64)
  assert (order == FloatLess)
    "-inf was not ordered below +inf"

gradualUnderflow :: Either String ()
gradualUnderflow = do
  minimumNormal <- bits Float32 0x00800000
  two <- mapLeft show (floatDecimalLiteral Float32 "2.0")
  half <- mapLeft show (applyFloatOperator FloatDivide minimumNormal two)
  assert (floatBits half == 0x00400000)
    ("minimum normal / 2 did not retain subnormal: " <> show (floatBits half))
  case classifyFloat half of
    FloatFinite _ -> Right ()
    other -> Left ("subnormal stopped being finite: " <> show other)

subnormalTie :: Either String ()
subnormalTie = do
  minimumSubnormal <- bits Float32 0x00000001
  two <- mapLeft show (floatDecimalLiteral Float32 "2.0")
  half <- mapLeft show (applyFloatOperator FloatDivide minimumSubnormal two)
  assert (half == positiveZero Float32)
    ("half-min-subnormal tie did not round to even zero: " <> show (floatBits half))

overflowRule :: Either String ()
overflowRule = do
  maximumFinite <- bits Float32 0x7f7fffff
  two <- mapLeft show (floatDecimalLiteral Float32 "2.0")
  overflow <- mapLeft show (applyFloatOperator FloatMultiply maximumFinite two)
  assert (overflow == positiveInfinity Float32)
    ("finite overflow did not produce source-declared +inf: " <> show (classifyFloat overflow))

formatMismatch :: Either String ()
formatMismatch = do
  left <- mapLeft show (floatDecimalLiteral Float32 "1.0")
  right <- mapLeft show (floatDecimalLiteral Float64 "1.0")
  case applyFloatOperator FloatAdd left right of
    Left (FloatFormatMismatch Float32 Float64) -> Right ()
    other -> Left ("mixed F32/F64 operation did not reject: " <> show other)

strictProfileAccepted :: Either String ()
strictProfileAccepted = do
  _ <- mapLeft show (checkFloatRealizationProfile (strictFloatRealizationProfile Float32))
  _ <- mapLeft show (checkFloatRealizationProfile (strictFloatRealizationProfile Float64))
  Right ()

fastMathRejects :: Either String ()
fastMathRejects = mapM_ reject
  [ FloatReassociation
  , FloatContraction
  , FloatAssumeNoNaN
  , FloatAssumeNoInfinity
  , FloatIgnoreSignedZero
  , FloatFlushToZero
  , FloatApproximateArithmetic
  ]
  where
    reject weakening =
      let profile = (strictFloatRealizationProfile Float32)
            { floatRealizationWeakenings = Set.singleton weakening }
      in case checkFloatRealizationProfile profile of
          Left (FloatRealizationSemanticWeakening weakenings)
            | weakenings == Set.singleton weakening -> Right ()
          other -> Left ("weakening was not rejected exactly: " <> show (weakening, other))

targetModeRejects :: Either String ()
targetModeRejects = do
  let wrongRounding = (strictFloatRealizationProfile Float64)
        { floatRealizationRoundingMode = FloatOtherRounding "toward-zero" }
  case checkFloatRealizationProfile wrongRounding of
    Left (FloatRealizationRoundingMismatch (FloatOtherRounding "toward-zero")) -> Right ()
    other -> Left ("wrong target rounding was admitted: " <> show other)
  let ftz = (strictFloatRealizationProfile Float32)
        { floatRealizationGradualUnderflow = False }
  case checkFloatRealizationProfile ftz of
    Left FloatRealizationFlushesSubnormals -> Right ()
    other -> Left ("flush-to-zero target was admitted: " <> show other)

bits :: FloatFormat -> Integer -> Either String FloatValue
bits format raw = mapLeft show (floatFromBits format (fromInteger raw))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
