module Phil.Core.UnicodeChar
  ( UnicodeScalar
  , UnicodeCharError (..)
  , UnicodeCharRealizationProfile (..)
  , UnicodeCharRealizationError (..)
  , unicodeCharCoreType
  , unicodeCharTypeFromCoreType
  , unicodeScalar
  , unicodeScalarCodePoint
  , strictUnicodeCharRealizationProfile
  , checkUnicodeCharRealization
  ) where

import Data.Text (Text)
import Phil.Core.Syntax
  ( RefSort (..)
  , Ty (..)
  )

-- | One Unicode scalar value, represented semantically by its integer code point.
-- The constructor is hidden so surrogates and out-of-range values cannot become
-- Phil Char values through this authority.
newtype UnicodeScalar = UnicodeScalar
  { unicodeScalarCodePoint :: Integer
  }
  deriving (Eq, Ord, Show)

data UnicodeCharError
  = UnicodeCharCodePointOutOfRange Integer
  | UnicodeCharSurrogateCodePoint Integer
  deriving (Eq, Ord, Show)

-- | Exact semantic identity for the Phase-1 Char scalar. This deliberately does
-- not claim any particular backend byte/code-unit representation.
unicodeCharCoreType :: Ty
unicodeCharCoreType =
  TyOpaqueSorted "Char" (SortOpaque "phil.unicode.scalar.v1")

unicodeCharTypeFromCoreType :: Ty -> Bool
unicodeCharTypeFromCoreType ty = ty == unicodeCharCoreType

unicodeScalar :: Integer -> Either UnicodeCharError UnicodeScalar
unicodeScalar codePoint
  | codePoint < 0 || codePoint > 0x10ffff =
      Left (UnicodeCharCodePointOutOfRange codePoint)
  | codePoint >= 0xd800 && codePoint <= 0xdfff =
      Left (UnicodeCharSurrogateCodePoint codePoint)
  | otherwise = Right (UnicodeScalar codePoint)

-- | A backend is free to choose a representation only when its checked relation
-- preserves the source scalar domain exactly. These are semantic facts, not a
-- request for any particular machine integer or Unicode encoding.
data UnicodeCharRealizationProfile = UnicodeCharRealizationProfile
  { unicodeCharRealizationCoversAllScalars :: Bool
  , unicodeCharRealizationRoundTripsExactly :: Bool
  , unicodeCharRealizationLocaleIndependent :: Bool
  , unicodeCharRealizationNoCodeUnitReinterpretation :: Bool
  }
  deriving (Eq, Ord, Show)

data UnicodeCharRealizationError
  = UnicodeCharRealizationIncompleteScalarDomain
  | UnicodeCharRealizationNotExactRoundTrip
  | UnicodeCharRealizationLocaleDependent
  | UnicodeCharRealizationCodeUnitReinterpretation
  deriving (Eq, Ord, Show)

strictUnicodeCharRealizationProfile :: UnicodeCharRealizationProfile
strictUnicodeCharRealizationProfile = UnicodeCharRealizationProfile
  { unicodeCharRealizationCoversAllScalars = True
  , unicodeCharRealizationRoundTripsExactly = True
  , unicodeCharRealizationLocaleIndependent = True
  , unicodeCharRealizationNoCodeUnitReinterpretation = True
  }

checkUnicodeCharRealization
  :: UnicodeCharRealizationProfile
  -> Either UnicodeCharRealizationError ()
checkUnicodeCharRealization profile
  | not (unicodeCharRealizationCoversAllScalars profile) =
      Left UnicodeCharRealizationIncompleteScalarDomain
  | not (unicodeCharRealizationRoundTripsExactly profile) =
      Left UnicodeCharRealizationNotExactRoundTrip
  | not (unicodeCharRealizationLocaleIndependent profile) =
      Left UnicodeCharRealizationLocaleDependent
  | not (unicodeCharRealizationNoCodeUnitReinterpretation profile) =
      Left UnicodeCharRealizationCodeUnitReinterpretation
  | otherwise = Right ()
