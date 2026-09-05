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
data ScalarType
  = ScalarBool
  | ScalarUInt Int
  deriving (Eq, Ord, Show)

-- | Closed scalar values. Keeping the width on UInt literals makes the value
-- self-describing at representation boundaries and prevents accidental
-- widening/narrowing by convention.
data ScalarLiteral
  = ScalarBoolLiteral Bool
  | ScalarUIntLiteral Int Integer
  deriving (Eq, Ord, Show)

scalarLiteralType :: ScalarLiteral -> ScalarType
scalarLiteralType literal = case literal of
  ScalarBoolLiteral _ -> ScalarBool
  ScalarUIntLiteral width _ -> ScalarUInt width

scalarLiteralInRange :: ScalarLiteral -> Bool
scalarLiteralInRange literal = case literal of
  ScalarBoolLiteral _ -> True
  ScalarUIntLiteral width value ->
    width > 0 && value >= 0 && value < (2 ^ width)

renderScalarType :: ScalarType -> Text
renderScalarType scalarType = case scalarType of
  ScalarBool -> "bool"
  ScalarUInt width -> "u" <> Text.pack (show width)

renderScalarLiteral :: ScalarLiteral -> Text
renderScalarLiteral literal = case literal of
  ScalarBoolLiteral value ->
    renderScalarType ScalarBool <> ":" <> if value then "true" else "false"
  ScalarUIntLiteral width value ->
    renderScalarType (ScalarUInt width) <> ":" <> Text.pack (show value)
