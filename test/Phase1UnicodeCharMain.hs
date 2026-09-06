{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Protocol.MessageAdmissibility (intrinsicBoundaryMessageType)
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , RefSort (..)
  , Ty (..)
  )
import Phil.Core.UnicodeChar
  ( UnicodeCharError (..)
  , UnicodeCharRealizationError (..)
  , UnicodeCharRealizationProfile (..)
  , checkUnicodeCharRealization
  , strictUnicodeCharRealizationProfile
  , unicodeCharCoreType
  , unicodeCharTypeFromCoreType
  , unicodeScalar
  , unicodeScalarCodePoint
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , GrammarV1TypeAliasDecl (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-022 Char source type retains exact scalar identity" sourceTypeIdentity
    , test "EXEC-022 Char values are unrestricted immutable scalars" sourceTypeMode
    , test "EXEC-022 Char is an intrinsic Message scalar" sourceMessageCompetence
    , test "EXEC-022 Unicode scalar boundary values accept exactly" scalarBoundaries
    , test "EXEC-022 surrogates and out-of-range code points reject" invalidScalarsReject
    , test "EXEC-022 Char never collapses to byte or UTF code-unit identity" semanticIdentityIsNotRepresentation
    , test "EXEC-022 exact backend scalar correspondence is admitted" strictRealizationAccepts
    , test "EXEC-022 backend representation drift rejects explicitly" realizationMutationsReject
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

sourceTypeIdentity :: Either String ()
sourceTypeIdentity = do
  sourceType <- parseAliasType "type Character = Char;"
  assert (sourceType == GrammarV1UnsignedType "Char")
    ("parser did not preserve Char primitive carrier: " <> show sourceType)
  assert (grammarV1PrimitiveType sourceType == Just unicodeCharCoreType)
    "Char did not elaborate to exact Unicode scalar Core identity"
  assert (unicodeCharTypeFromCoreType unicodeCharCoreType)
    "exact Char Core identity was not recognized"

sourceTypeMode :: Either String ()
sourceTypeMode = do
  checked <- case grammarV1CheckedTypeMode
      emptyStaticContext emptySurfaceState (GrammarV1UnsignedType "Char") of
    Just (Right (mode, _)) -> Right mode
    other -> Left ("Char checked mode did not resolve: " <> show other)
  assert (checkedBindingMode checked == Unrestricted)
    ("Char mode was not unrestricted: " <> show (checkedBindingMode checked))

sourceMessageCompetence :: Either String ()
sourceMessageCompetence =
  assert (intrinsicBoundaryMessageType unicodeCharCoreType)
    "Char did not receive intrinsic Message competence"

scalarBoundaries :: Either String ()
scalarBoundaries = do
  mapM_ assertScalar
    [ 0x0000
    , 0x0041
    , 0xd7ff
    , 0xe000
    , 0xffff
    , 0x10000
    , 0x10ffff
    ]
  where
    assertScalar codePoint = do
      scalar <- mapLeft show (unicodeScalar codePoint)
      assert (unicodeScalarCodePoint scalar == codePoint)
        ("scalar code point changed: " <> show codePoint)

invalidScalarsReject :: Either String ()
invalidScalarsReject = do
  assert
    (unicodeScalar (-1) == Left (UnicodeCharCodePointOutOfRange (-1)))
    "negative code point was admitted"
  assert
    (unicodeScalar 0xd800 == Left (UnicodeCharSurrogateCodePoint 0xd800))
    "first surrogate was admitted"
  assert
    (unicodeScalar 0xdfff == Left (UnicodeCharSurrogateCodePoint 0xdfff))
    "last surrogate was admitted"
  assert
    (unicodeScalar 0x110000 == Left (UnicodeCharCodePointOutOfRange 0x110000))
    "code point above Unicode maximum was admitted"

semanticIdentityIsNotRepresentation :: Either String ()
semanticIdentityIsNotRepresentation = do
  assert (unicodeCharCoreType /= TyUInt 8)
    "Char collapsed to one-byte integer representation"
  assert (unicodeCharCoreType /= TyUInt 16)
    "Char collapsed to one UTF-16 code-unit representation"
  assert
    (unicodeCharCoreType /= TyOpaqueSorted "Char" (SortOpaque "host-char"))
    "Char accepted a host/locale representation identity"
  supplementary <- mapLeft show (unicodeScalar 0x1f600)
  assert (unicodeScalarCodePoint supplementary == 0x1f600)
    "supplementary scalar did not remain one semantic Char"

strictRealizationAccepts :: Either String ()
strictRealizationAccepts =
  mapLeft show (checkUnicodeCharRealization strictUnicodeCharRealizationProfile)

realizationMutationsReject :: Either String ()
realizationMutationsReject = do
  assert
    (checkUnicodeCharRealization strictUnicodeCharRealizationProfile
      { unicodeCharRealizationCoversAllScalars = False }
      == Left UnicodeCharRealizationIncompleteScalarDomain)
    "one-byte/incomplete scalar domain was admitted"
  assert
    (checkUnicodeCharRealization strictUnicodeCharRealizationProfile
      { unicodeCharRealizationRoundTripsExactly = False }
      == Left UnicodeCharRealizationNotExactRoundTrip)
    "lossy scalar representation was admitted"
  assert
    (checkUnicodeCharRealization strictUnicodeCharRealizationProfile
      { unicodeCharRealizationLocaleIndependent = False }
      == Left UnicodeCharRealizationLocaleDependent)
    "locale-dependent character representation was admitted"
  assert
    (checkUnicodeCharRealization strictUnicodeCharRealizationProfile
      { unicodeCharRealizationNoCodeUnitReinterpretation = False }
      == Left UnicodeCharRealizationCodeUnitReinterpretation)
    "UTF code-unit reinterpretation was admitted"

parseAliasType :: String -> Either String GrammarV1Type
parseAliasType source = do
  parsed <- mapLeft show $
    parseGrammarV1StructuralSource "exec-022.phil" (fromString source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1TypeAliasDeclaration alias ->
        Right (locatedValue (grammarV1TypeAliasTarget alias))
      other -> Left ("expected type alias, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show declarations)

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
