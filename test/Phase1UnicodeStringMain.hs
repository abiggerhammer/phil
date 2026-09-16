{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Protocol.MessageAdmissibility (intrinsicBoundaryMessageType)
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Core.UnicodeChar
  ( UnicodeScalar
  , unicodeScalar
  )
import Phil.Core.UnicodeString
  ( UnicodeString
  , UnicodeStringRealizationError (..)
  , UnicodeStringRealizationProfile (..)
  , checkUnicodeStringRealization
  , strictUnicodeStringRealizationProfile
  , unicodeString
  , unicodeStringCodePoints
  , unicodeStringCoreType
  , unicodeStringTypeFromCoreType
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
    [ test "EXEC-023 String source type retains exact semantic identity" sourceTypeIdentity
    , test "EXEC-023 String values are unrestricted immutable values" sourceTypeMode
    , test "EXEC-023 String is an intrinsic Message value" sourceMessageCompetence
    , test "EXEC-023 empty ASCII non-ASCII and multi-scalar values are exact" exactScalarSequences
    , test "EXEC-023 canonically equivalent scalar sequences remain distinct" normalizationDoesNotCollapseIdentity
    , test "EXEC-023 String identity is not encoded bytes or host storage" semanticIdentityIsNotRepresentation
    , test "EXEC-023 semantic copying permits representation sharing" semanticCopyIsValuePreserving
    , test "EXEC-023 realization drift rejects explicitly" realizationMutationsReject
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

sourceTypeIdentity :: Either String ()
sourceTypeIdentity = do
  sourceType <- parseAliasType "type TextValue = String;"
  assert (sourceType == GrammarV1UnsignedType "String")
    ("parser did not preserve String primitive carrier: " <> show sourceType)
  assert (grammarV1PrimitiveType sourceType == Just unicodeStringCoreType)
    "String did not elaborate to exact semantic String Core identity"
  assert (unicodeStringTypeFromCoreType unicodeStringCoreType)
    "exact String Core identity was not recognized"

sourceTypeMode :: Either String ()
sourceTypeMode = do
  checked <- case grammarV1CheckedTypeMode
      emptyStaticContext emptySurfaceState (GrammarV1UnsignedType "String") of
    Just (Right (mode, _)) -> Right mode
    other -> Left ("String checked mode did not resolve: " <> show other)
  assert (checkedBindingMode checked == Unrestricted)
    ("String mode was not unrestricted: " <> show (checkedBindingMode checked))

sourceMessageCompetence :: Either String ()
sourceMessageCompetence =
  assert (intrinsicBoundaryMessageType unicodeStringCoreType)
    "String did not receive intrinsic Message competence"

exactScalarSequences :: Either String ()
exactScalarSequences = do
  empty <- stringValue []
  ascii <- stringValue [0x48, 0x69]
  nonAscii <- stringValue [0x03bb]
  multi <- stringValue [0x41, 0x1f600, 0x03bb]
  assert (unicodeStringCodePoints empty == []) "empty String changed"
  assert (unicodeStringCodePoints ascii == [0x48, 0x69]) "ASCII String changed"
  assert (unicodeStringCodePoints nonAscii == [0x03bb]) "non-ASCII String changed"
  assert (unicodeStringCodePoints multi == [0x41, 0x1f600, 0x03bb])
    "multi-scalar String changed"

normalizationDoesNotCollapseIdentity :: Either String ()
normalizationDoesNotCollapseIdentity = do
  composed <- stringValue [0x00e9]
  decomposed <- stringValue [0x0065, 0x0301]
  assert (composed /= decomposed)
    "canonically equivalent but distinct scalar sequences were normalized implicitly"
  assert (unicodeStringCodePoints composed == [0x00e9])
    "composed sequence changed"
  assert (unicodeStringCodePoints decomposed == [0x0065, 0x0301])
    "decomposed sequence changed"

semanticIdentityIsNotRepresentation :: Either String ()
semanticIdentityIsNotRepresentation = do
  assert (unicodeStringCoreType /= TyBytes (RefNat 0))
    "String collapsed to Bytes"
  assert (unicodeStringCoreType /= TyOpaque "host-string")
    "String collapsed to a host string object"
  assert (unicodeStringCoreType /= TyOpaque "nul-terminated")
    "String collapsed to NUL-terminated storage"

semanticCopyIsValuePreserving :: Either String ()
semanticCopyIsValuePreserving = do
  original <- stringValue [0x41, 0x1f600]
  let copied = original
  assert (copied == original)
    "semantic copy changed String value"
  mapLeft show (checkUnicodeStringRealization strictUnicodeStringRealizationProfile)

realizationMutationsReject :: Either String ()
realizationMutationsReject = do
  assert
    (checkUnicodeStringRealization strictUnicodeStringRealizationProfile
      { unicodeStringRealizationExactScalarSequence = False }
      == Left UnicodeStringRealizationScalarSequenceDrift)
    "scalar-sequence drift was admitted"
  assert
    (checkUnicodeStringRealization strictUnicodeStringRealizationProfile
      { unicodeStringRealizationImmutable = False }
      == Left UnicodeStringRealizationMutable)
    "mutable String realization was admitted"
  assert
    (checkUnicodeStringRealization strictUnicodeStringRealizationProfile
      { unicodeStringRealizationNoImplicitNormalization = False }
      == Left UnicodeStringRealizationImplicitNormalization)
    "implicit Unicode normalization was admitted"
  assert
    (checkUnicodeStringRealization strictUnicodeStringRealizationProfile
      { unicodeStringRealizationNoImplicitEncoding = False }
      == Left UnicodeStringRealizationImplicitEncoding)
    "implicit text encoding was admitted"

stringValue :: [Integer] -> Either String UnicodeString
stringValue codePoints = do
  scalars <- mapM scalarValue codePoints
  Right (unicodeString scalars)

scalarValue :: Integer -> Either String UnicodeScalar
scalarValue = mapLeft show . unicodeScalar

parseAliasType :: String -> Either String GrammarV1Type
parseAliasType source = do
  parsed <- mapLeft show $
    parseGrammarV1StructuralSource "exec-023.phil" (Text.pack source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1TypeAliasDeclaration alias ->
        Right (locatedValue (grammarV1TypeAliasTarget alias))
      other -> Left ("expected type alias, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show declarations)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
