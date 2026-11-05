{-# LANGUAGE OverloadedStrings #-}

-- Regression for the historical 430aba3/FLOAT-BOUNDARY representation
-- escape. Uses only the public FloatValue construction and numeric consumers.
module Main (main) where

import Control.Monad (unless)
import Data.Word (Word64)
import Phil.Core.FloatArithmetic
  ( FloatFormat (..)
  , FloatSemanticError (..)
  , floatBits
  , floatFormat
  , floatFromBits
  , positiveZero
  )
import Phil.Core.NumericConversion
  ( NumericConversionResult (..)
  , NumericType (..)
  , NumericValue (..)
  , convertNumericValue
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let tooWide = 0x100000000 :: Word64
      maximalF32 = 0xffffffff :: Word64
      maximalF64 = maxBound :: Word64
      checks =
        [ ("F32 rejects the first out-of-range high bit",
            floatFromBits Float32 tooWide ==
              Left (FloatBitsOutOfRange Float32 tooWide))
        , ("F32 accepts its complete 32-bit representation",
            case floatFromBits Float32 maximalF32 of
              Right v -> floatFormat v == Float32 && floatBits v == maximalF32
              Left _ -> False)
        , ("F64 accepts all 64 representation bits",
            case floatFromBits Float64 maximalF64 of
              Right v -> floatFormat v == Float64 && floatBits v == maximalF64
              Left _ -> False)
        , ("numeric conversion of a validated F32 retains exact format and bits",
            case floatFromBits Float32 0x3f800000 of
              Left _ -> False
              Right v -> case convertNumericValue
                  (NumericFloatType Float32) (NumericFloatValue v) of
                Right result -> numericConversionValue result == NumericFloatValue v
                Left _ -> False)
        , ("same-format numeric conversion of a valid F64 remains unchanged",
            let v = positiveZero Float64
            in case convertNumericValue
                (NumericFloatType Float64) (NumericFloatValue v) of
              Right result -> numericConversionValue result == NumericFloatValue v
              Left _ -> False)
        ]
  mapM_ report checks
  unless (all snd checks) exitFailure
  where
    report (label, True) = putStrLn ("PASS: FLOAT-BOUNDARY " ++ label)
    report (label, False) = putStrLn ("FAIL: FLOAT-BOUNDARY " ++ label)
