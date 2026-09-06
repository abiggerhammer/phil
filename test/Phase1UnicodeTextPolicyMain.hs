{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.TextEncoding
  ( TextEncoding (UTF8)
  , encodeText
  , encodedTextBytesType
  )
import Phil.Core.UnicodeChar
  ( unicodeScalar
  )
import Phil.Core.UnicodeString
  ( unicodeString
  , unicodeStringCodePoints
  )
import Phil.Core.UnicodeTextPolicy
  ( StringIndexUnit (..)
  , UnicodeDataVersion
  , UnicodeTextAlgorithm (..)
  , UnicodeTextPolicyError (..)
  , checkStringIndexUnit
  , unicodeAlgorithmContract
  , unicodeAlgorithmContractAlgorithm
  , unicodeAlgorithmContractVersion
  , unicodeDataVersion
  )
import Phil.Core.Syntax (RefTerm (RefNat), Ty (TyBytes))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-026 Unicode-data version is mandatory and nonempty" versionRequired
    , test "EXEC-026 algorithm contract retains exact Unicode version" exactVersionBinding
    , test "EXEC-026 NFC and NFD remain distinct named operations" normalizationOperationsDistinct
    , test "EXEC-026 version changes produce distinct algorithm contracts" versionSensitiveContractsDistinct
    , test "EXEC-026 ambient property/locale/display parameters reject" ambientParametersReject
    , test "EXEC-026 explicit locale/profile parameters accept" explicitParametersAccept
    , test "EXEC-026 primitive String semantics do not normalize" primitiveStringDoesNotNormalize
    , test "EXEC-026 String indexing requires an explicit unit" ambiguousIndexingRejects
    , test "EXEC-026 byte indexing is a Bytes operation, not a String unit" byteIndexingRejects
    , test "EXEC-026 explicit scalar indexing is admitted" scalarIndexingAccepts
    , test "EXEC-026 grapheme indexing carries an exact Unicode version" graphemeIndexingIsVersioned
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

versionRequired :: Either String ()
versionRequired = do
  expectLeft UnicodeDataVersionRequired (unicodeDataVersion "")
  expectLeft UnicodeDataVersionRequired (unicodeDataVersion "   ")

exactVersionBinding :: Either String ()
exactVersionBinding = do
  version <- mapLeft show (unicodeDataVersion "15.1.0")
  contract <- mapLeft show (unicodeAlgorithmContract version UnicodeCaseFold)
  assert (unicodeAlgorithmContractVersion contract == version)
    "algorithm contract lost exact Unicode-data version"
  assert (unicodeAlgorithmContractAlgorithm contract == UnicodeCaseFold)
    "algorithm contract changed operation identity"

normalizationOperationsDistinct :: Either String ()
normalizationOperationsDistinct = do
  version <- mapLeft show (unicodeDataVersion "15.1.0")
  nfc <- mapLeft show (unicodeAlgorithmContract version UnicodeNormalizeNFC)
  nfd <- mapLeft show (unicodeAlgorithmContract version UnicodeNormalizeNFD)
  assert (nfc /= nfd) "NFC and NFD collapsed to one operation identity"

versionSensitiveContractsDistinct :: Either String ()
versionSensitiveContractsDistinct = do
  oldVersion <- mapLeft show (unicodeDataVersion "15.1.0")
  newVersion <- mapLeft show (unicodeDataVersion "16.0.0")
  oldContract <- mapLeft show $
    unicodeAlgorithmContract oldVersion UnicodeGraphemeSegmentation
  newContract <- mapLeft show $
    unicodeAlgorithmContract newVersion UnicodeGraphemeSegmentation
  assert (oldContract /= newContract)
    "Unicode-version-sensitive algorithm contracts collapsed across versions"

ambientParametersReject :: Either String ()
ambientParametersReject = do
  version <- mapLeft show (unicodeDataVersion "15.1.0")
  expectAlgorithmParameterReject version (UnicodeCaseMap "")
  expectAlgorithmParameterReject version (UnicodePropertyLookup "")
  expectAlgorithmParameterReject version (UnicodeCollation "")
  expectAlgorithmParameterReject version (UnicodeDisplayWidth "")

explicitParametersAccept :: Either String ()
explicitParametersAccept = do
  version <- mapLeft show (unicodeDataVersion "15.1.0")
  _ <- mapLeft show $
    unicodeAlgorithmContract version (UnicodeCaseMap "und")
  _ <- mapLeft show $
    unicodeAlgorithmContract version (UnicodePropertyLookup "General_Category")
  _ <- mapLeft show $
    unicodeAlgorithmContract version (UnicodeCollation "und")
  _ <- mapLeft show $
    unicodeAlgorithmContract version (UnicodeDisplayWidth "terminal-v1")
  Right ()

primitiveStringDoesNotNormalize :: Either String ()
primitiveStringDoesNotNormalize = do
  composedScalar <- mapLeft show (unicodeScalar 0x00e9)
  eScalar <- mapLeft show (unicodeScalar 0x0065)
  combiningAcute <- mapLeft show (unicodeScalar 0x0301)
  let composed = unicodeString [composedScalar]
      decomposed = unicodeString [eScalar, combiningAcute]
  assert (unicodeStringCodePoints composed == [0x00e9])
    "composed primitive String changed scalar sequence"
  assert (unicodeStringCodePoints decomposed == [0x0065, 0x0301])
    "decomposed primitive String changed scalar sequence"
  assert (composed /= decomposed)
    "primitive String semantics performed implicit Unicode normalization"

ambiguousIndexingRejects :: Either String ()
ambiguousIndexingRejects =
  expectLeft StringIndexUnitRequired (checkStringIndexUnit Nothing)

byteIndexingRejects :: Either String ()
byteIndexingRejects = do
  expectLeft StringByteIndexingRequiresBytes
    (checkStringIndexUnit (Just StringByteIndex))
  ascii <- mapLeft show (unicodeScalar 0x41)
  encoded <- mapLeft show (encodeText UTF8 (unicodeString [ascii]))
  assert (encodedTextBytesType encoded == TyBytes (RefNat 1))
    "explicit UTF-8 byte subject did not retain Bytes indexing domain"

scalarIndexingAccepts :: Either String ()
scalarIndexingAccepts = do
  unit <- mapLeft show (checkStringIndexUnit (Just StringUnicodeScalarIndex))
  assert (unit == StringUnicodeScalarIndex)
    "explicit Unicode-scalar indexing changed unit"

graphemeIndexingIsVersioned :: Either String ()
graphemeIndexingIsVersioned = do
  version <- mapLeft show (unicodeDataVersion "15.1.0")
  unit <- mapLeft show $
    checkStringIndexUnit (Just (StringGraphemeClusterIndex version))
  assert (unit == StringGraphemeClusterIndex version)
    "grapheme indexing lost exact Unicode-data version"

expectAlgorithmParameterReject
  :: UnicodeDataVersion
  -> UnicodeTextAlgorithm
  -> Either String ()
expectAlgorithmParameterReject version algorithm =
  case unicodeAlgorithmContract version algorithm of
    Left (UnicodeAlgorithmParameterRequired actual)
      | actual == algorithm -> Right ()
    other -> Left ("expected explicit algorithm parameter rejection, got " <> show other)

expectLeft :: (Eq e, Show e, Show a) => e -> Either e a -> Either String ()
expectLeft expected actual = case actual of
  Left err | err == expected -> Right ()
  other -> Left ("expected " <> show expected <> ", got " <> show other)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
