{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Scalar
  ( ScalarType (..)
  , ScalarLiteral (..)
  , scalarLiteralType
  , scalarLiteralInRange
  , renderScalarType
  , renderScalarLiteral
  ) where

import Data.Text (Text)
import qualified Data.Text as Text

-- | Scalar types whose representation survives into the Systems and LLVM IRs.
-- Fixed-width signedness is semantic even when a target uses the same physical
-- bitvector carrier for signed and unsigned values.
data ScalarType
  = ScalarBool
  | ScalarUInt Int
  | ScalarSInt Int
  deriving (Eq, Ord, Show)

-- | Closed scalar values. Keeping width and signedness on integer literals makes
-- values self-describing at representation boundaries and prevents accidental
-- widening, narrowing, or signedness changes by convention.
data ScalarLiteral
  = ScalarBoolLiteral Bool
  | ScalarUIntLiteral Int Integer
  | ScalarSIntLiteral Int Integer
  deriving (Eq, Ord, Show)

scalarLiteralType :: ScalarLiteral -> ScalarType
scalarLiteralType literal = case literal of
  ScalarBoolLiteral _ -> ScalarBool
  ScalarUIntLiteral width _ -> ScalarUInt width
  ScalarSIntLiteral width _ -> ScalarSInt width

scalarLiteralInRange :: ScalarLiteral -> Bool
scalarLiteralInRange literal = case literal of
  ScalarBoolLiteral _ -> True
  ScalarUIntLiteral width value ->
    width > 0 && value >= 0 && value < (2 ^ width)
  ScalarSIntLiteral width value ->
    width > 0
      && value >= negate (2 ^ (width - 1))
      && value < 2 ^ (width - 1)

renderScalarType :: ScalarType -> Text
renderScalarType scalarType = case scalarType of
  ScalarBool -> "bool"
  ScalarUInt width -> "u" <> Text.pack (show width)
  ScalarSInt width -> "i" <> Text.pack (show width)

renderScalarLiteral :: ScalarLiteral -> Text
renderScalarLiteral literal = case literal of
  ScalarBoolLiteral value ->
    renderScalarType ScalarBool <> ":" <> if value then "true" else "false"
  ScalarUIntLiteral width value ->
    renderScalarType (ScalarUInt width) <> ":" <> Text.pack (show value)
  ScalarSIntLiteral width value ->
    renderScalarType (ScalarSInt width) <> ":" <> Text.pack (show value)
