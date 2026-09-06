{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.UnicodeString
  ( UnicodeString
  , UnicodeStringRealizationProfile (..)
  , UnicodeStringRealizationError (..)
  , unicodeStringCoreType
  , unicodeStringTypeFromCoreType
  , unicodeString
  , unicodeStringScalars
  , unicodeStringCodePoints
  , strictUnicodeStringRealizationProfile
  , checkUnicodeStringRealization
  ) where

import Phil.Core.Syntax
  ( RefSort (..)
  , Ty (..)
  )
import Phil.Core.UnicodeChar
  ( UnicodeScalar
  , unicodeScalarCodePoint
  )

-- | An immutable finite sequence of Phil Unicode scalar values. The constructor
-- is hidden so String identity is expressed only in terms of semantic Char
-- values, never bytes, UTF code units, host string objects, or storage layout.
newtype UnicodeString = UnicodeString
  { unicodeStringScalars :: [UnicodeScalar]
  }
  deriving (Eq, Ord, Show)

unicodeStringCoreType :: Ty
unicodeStringCoreType =
  TyOpaqueSorted "String" (SortOpaque "phil.unicode.string.v1")

unicodeStringTypeFromCoreType :: Ty -> Bool
unicodeStringTypeFromCoreType ty = ty == unicodeStringCoreType

unicodeString :: [UnicodeScalar] -> UnicodeString
unicodeString = UnicodeString

unicodeStringCodePoints :: UnicodeString -> [Integer]
unicodeStringCodePoints = map unicodeScalarCodePoint . unicodeStringScalars

-- | String realization is representation-neutral. Sharing immutable physical
-- storage is permitted; only the exact semantic scalar sequence matters.
data UnicodeStringRealizationProfile = UnicodeStringRealizationProfile
  { unicodeStringRealizationExactScalarSequence :: Bool
  , unicodeStringRealizationImmutable :: Bool
  , unicodeStringRealizationNoImplicitNormalization :: Bool
  , unicodeStringRealizationNoImplicitEncoding :: Bool
  }
  deriving (Eq, Ord, Show)

data UnicodeStringRealizationError
  = UnicodeStringRealizationScalarSequenceDrift
  | UnicodeStringRealizationMutable
  | UnicodeStringRealizationImplicitNormalization
  | UnicodeStringRealizationImplicitEncoding
  deriving (Eq, Ord, Show)

strictUnicodeStringRealizationProfile :: UnicodeStringRealizationProfile
strictUnicodeStringRealizationProfile = UnicodeStringRealizationProfile
  { unicodeStringRealizationExactScalarSequence = True
  , unicodeStringRealizationImmutable = True
  , unicodeStringRealizationNoImplicitNormalization = True
  , unicodeStringRealizationNoImplicitEncoding = True
  }

checkUnicodeStringRealization
  :: UnicodeStringRealizationProfile
  -> Either UnicodeStringRealizationError ()
checkUnicodeStringRealization profile
  | not (unicodeStringRealizationExactScalarSequence profile) =
      Left UnicodeStringRealizationScalarSequenceDrift
  | not (unicodeStringRealizationImmutable profile) =
      Left UnicodeStringRealizationMutable
  | not (unicodeStringRealizationNoImplicitNormalization profile) =
      Left UnicodeStringRealizationImplicitNormalization
  | not (unicodeStringRealizationNoImplicitEncoding profile) =
      Left UnicodeStringRealizationImplicitEncoding
  | otherwise = Right ()
