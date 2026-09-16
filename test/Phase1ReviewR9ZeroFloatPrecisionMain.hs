{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.FloatArithmetic
  ( FloatFormat (..)
  , FloatValue
  , floatBits
  , floatFromBits
  , negativeZero
  )
import Phil.Core.NumericConversion
  ( NumericConversionPrecision (..)
  , NumericConversionResult (..)
  , NumericType (..)
  , NumericValue (..)
  , convertNumericValue
  )
import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntType (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "REVIEW-R09 UInt zero -> F32 is exact" (integerZeroExact (NumericUIntValue 8 0) Float32)
    , test "REVIEW-R09 UInt zero -> F64 is exact" (integerZeroExact (NumericUIntValue 8 0) Float64)
    , test "REVIEW-R09 SInt zero -> F32 is exact" (integerZeroExact (NumericSIntValue (SIntLiteral (SIntType 8) 0)) Float32)
    , test "REVIEW-R09 SInt zero -> F64 is exact" (integerZeroExact (NumericSIntValue (SIntLiteral (SIntType 8) 0)) Float64)
    , test "REVIEW-R09 representative exact integer conversion stays exact" exactIntegerControl
    , test "REVIEW-R09 representative inexact integer conversion stays rounded" inexactIntegerControl
    , test "REVIEW-R09 nonzero F64 subnormal rounding to F32 zero stays rounded" nonzeroUnderflowControl
    , test "REVIEW-R09 negative floating zero width conversion stays exact" negativeZeroControl
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

integerZeroExact :: NumericValue -> FloatFormat -> Either String ()
integerZeroExact source format = do
  result <- mapLeft show (convertNumericValue (NumericFloatType format) source)
  assert (numericConversionPrecision result == NumericConversionExact)
    ("zero was not classified exact: " <> show result)
  value <- floatValue result
  assert (floatBits value == 0)
    ("integer zero did not convert to positive zero bits: " <> show (floatBits value))

exactIntegerControl :: Either String ()
exactIntegerControl = do
  result <- mapLeft show (convertNumericValue (NumericFloatType Float32) (NumericUIntValue 32 1))
  assert (numericConversionPrecision result == NumericConversionExact)
    ("exact integer conversion classification drifted: " <> show result)

inexactIntegerControl :: Either String ()
inexactIntegerControl = do
  result <- mapLeft show (convertNumericValue (NumericFloatType Float32) (NumericUIntValue 32 16777217))
  assert (numericConversionPrecision result == NumericConversionRounded)
    ("inexact integer conversion stopped reporting rounding: " <> show result)

nonzeroUnderflowControl :: Either String ()
nonzeroUnderflowControl = do
  tiny <- mapLeft show (floatFromBits Float64 1)
  result <- mapLeft show (convertNumericValue (NumericFloatType Float32) (NumericFloatValue tiny))
  assert (numericConversionPrecision result == NumericConversionRounded)
    ("nonzero underflow-to-zero was not classified rounded: " <> show result)
  value <- floatValue result
  assert (floatBits value == 0)
    ("minimum F64 subnormal did not round to F32 zero: " <> show (floatBits value))

negativeZeroControl :: Either String ()
negativeZeroControl = do
  result <- mapLeft show
    (convertNumericValue (NumericFloatType Float32) (NumericFloatValue (negativeZero Float64)))
  assert (numericConversionPrecision result == NumericConversionExact)
    ("negative-zero width conversion classification drifted: " <> show result)
  value <- floatValue result
  assert (floatBits value == 0x80000000)
    ("negative-zero sign was not preserved: " <> show (floatBits value))

floatValue :: NumericConversionResult -> Either String FloatValue
floatValue result = case numericConversionValue result of
  NumericFloatValue value -> Right value
  other -> Left ("expected floating conversion result, got " <> show other)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
