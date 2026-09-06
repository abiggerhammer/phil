{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.UnicodeTextPolicy
  ( UnicodeDataVersion
  , UnicodeTextAlgorithm (..)
  , UnicodeTextPolicyError (..)
  , UnicodeAlgorithmContract
  , StringIndexUnit (..)
  , unicodeDataVersion
  , unicodeDataVersionText
  , unicodeAlgorithmContract
  , unicodeAlgorithmContractVersion
  , unicodeAlgorithmContractAlgorithm
  , checkStringIndexUnit
  ) where

import Data.Text (Text)
import qualified Data.Text as Text

-- | Unicode database/version identity is explicit semantic input for every
-- algorithm whose meaning depends on evolving Unicode data. The constructor is
-- hidden so an empty/ambient version cannot enter the checked boundary.
newtype UnicodeDataVersion = UnicodeDataVersion
  { unicodeDataVersionText :: Text
  }
  deriving (Eq, Ord, Show)

data UnicodeTextAlgorithm
  = UnicodeNormalizeNFC
  | UnicodeNormalizeNFD
  | UnicodeCaseFold
  | UnicodePropertyLookup Text
  | UnicodeGraphemeSegmentation
  | UnicodeCollation Text
  | UnicodeDisplayWidth Text
  deriving (Eq, Ord, Show)

data UnicodeTextPolicyError
  = UnicodeDataVersionRequired
  | UnicodeAlgorithmParameterRequired UnicodeTextAlgorithm
  | StringIndexUnitRequired
  | StringByteIndexingRequiresBytes
  deriving (Eq, Ord, Show)

-- | Checked algorithm competence is a pair of an exact algorithm description
-- and an exact Unicode-data version. This deliberately does not implement the
-- algorithm: a qualified/versioned library or provider must supply that later.
data UnicodeAlgorithmContract = UnicodeAlgorithmContract
  { unicodeAlgorithmContractVersion :: UnicodeDataVersion
  , unicodeAlgorithmContractAlgorithm :: UnicodeTextAlgorithm
  }
  deriving (Eq, Ord, Show)

-- | A later String indexing/slicing surface must state a semantic unit. Byte
-- indexing is represented only so this boundary can reject it explicitly:
-- byte positions belong to Bytes, not semantic String values.
data StringIndexUnit
  = StringByteIndex
  | StringUnicodeScalarIndex
  | StringGraphemeClusterIndex UnicodeDataVersion
  deriving (Eq, Ord, Show)

unicodeDataVersion :: Text -> Either UnicodeTextPolicyError UnicodeDataVersion
unicodeDataVersion raw
  | Text.null (Text.strip raw) = Left UnicodeDataVersionRequired
  | otherwise = Right (UnicodeDataVersion raw)

unicodeAlgorithmContract
  :: UnicodeDataVersion
  -> UnicodeTextAlgorithm
  -> Either UnicodeTextPolicyError UnicodeAlgorithmContract
unicodeAlgorithmContract version algorithm = do
  validateAlgorithmParameter algorithm
  Right UnicodeAlgorithmContract
    { unicodeAlgorithmContractVersion = version
    , unicodeAlgorithmContractAlgorithm = algorithm
    }

-- | Primitive String semantics provide no default indexing unit. Explicit
-- scalar indexing is version-independent; grapheme indexing carries the exact
-- Unicode-data version that defines the segmentation relation.
checkStringIndexUnit
  :: Maybe StringIndexUnit
  -> Either UnicodeTextPolicyError StringIndexUnit
checkStringIndexUnit maybeUnit = case maybeUnit of
  Nothing -> Left StringIndexUnitRequired
  Just StringByteIndex -> Left StringByteIndexingRequiresBytes
  Just unit -> Right unit

validateAlgorithmParameter
  :: UnicodeTextAlgorithm
  -> Either UnicodeTextPolicyError ()
validateAlgorithmParameter algorithm = case algorithm of
  UnicodePropertyLookup propertyName
    | Text.null (Text.strip propertyName) ->
        Left (UnicodeAlgorithmParameterRequired algorithm)
  UnicodeCollation locale
    | Text.null (Text.strip locale) ->
        Left (UnicodeAlgorithmParameterRequired algorithm)
  UnicodeDisplayWidth profile
    | Text.null (Text.strip profile) ->
        Left (UnicodeAlgorithmParameterRequired algorithm)
  _ -> Right ()
