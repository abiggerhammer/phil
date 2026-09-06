module Main (main) where

import Data.Word (Word8)
import Phil.Core.Syntax
  ( RefTerm (..)
  , Ty (..)
  )
import Phil.Core.TextEncoding
  ( TextEncoding (..)
  , TextEncodingError (..)
  , checkEncodedTextCorrespondence
  , checkTextEncodingCorrespondence
  , decodeText
  , encodeText
  , encodedTextBytes
  , encodedTextBytesType
  , encodedTextEncoding
  )
import Phil.Core.UnicodeChar (unicodeScalar)
import Phil.Core.UnicodeString
  ( UnicodeString
  , unicodeString
  , unicodeStringCodePoints
  , unicodeStringCoreType
  )
import Phil.Core.Value
  ( EqualityBoundary (..)
  , compareTypes
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-025 UTF-8 ASCII encoding is exact" asciiEncoding
    , test "EXEC-025 UTF-8 BMP and supplementary encoding is exact" unicodeEncoding
    , test "EXEC-025 UTF-8 round-trip preserves exact scalar sequence" utf8RoundTrip
    , test "EXEC-025 composed and decomposed text remain distinct" normalizationRemainsExplicit
    , test "EXEC-025 invalid UTF-8 rejects as checked decoding failure" invalidUtf8Rejects
    , test "EXEC-025 encoded subject carries exact Bytes length" exactBytesSubject
    , test "EXEC-025 correspondence rejects byte or subject mismatch" correspondenceRejectsMismatch
    , test "EXEC-025 String and Bytes remain incompatible types" noImplicitStringBytesConversion
    , test "EXEC-025 alternate encoding identity cannot masquerade as UTF-8" alternateEncodingSeparation
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

asciiEncoding :: Either String ()
asciiEncoding = do
  source <- makeString [0x41, 0x42, 0x43]
  encoded <- mapLeft show (encodeText UTF8 source)
  assert (encodedTextEncoding encoded == UTF8) "encoding identity drifted"
  assert (encodedTextBytes encoded == [0x41, 0x42, 0x43])
    ("ASCII UTF-8 bytes changed: " <> show (encodedTextBytes encoded))
  mapLeft show (checkEncodedTextCorrespondence encoded)

unicodeEncoding :: Either String ()
unicodeEncoding = do
  source <- makeString [0x03bb, 0x1f600]
  encoded <- mapLeft show (encodeText UTF8 source)
  assert
    (encodedTextBytes encoded == [0xce, 0xbb, 0xf0, 0x9f, 0x98, 0x80])
    ("Unicode UTF-8 bytes changed: " <> show (encodedTextBytes encoded))

utf8RoundTrip :: Either String ()
utf8RoundTrip = do
  source <- makeString [0x00, 0x7f, 0x80, 0x7ff, 0x800, 0x20ac, 0x1f600, 0x10ffff]
  encoded <- mapLeft show (encodeText UTF8 source)
  decoded <- mapLeft show (decodeText UTF8 (encodedTextBytes encoded))
  assert (decoded == source)
    ("UTF-8 round-trip changed scalar sequence: " <> show (unicodeStringCodePoints decoded))

normalizationRemainsExplicit :: Either String ()
normalizationRemainsExplicit = do
  composed <- makeString [0x00e9]
  decomposed <- makeString [0x0065, 0x0301]
  composedEncoded <- mapLeft show (encodeText UTF8 composed)
  decomposedEncoded <- mapLeft show (encodeText UTF8 decomposed)
  assert (encodedTextBytes composedEncoded /= encodedTextBytes decomposedEncoded)
    "UTF-8 encoding normalized canonically equivalent Strings"
  composedDecoded <- mapLeft show (decodeText UTF8 (encodedTextBytes composedEncoded))
  decomposedDecoded <- mapLeft show (decodeText UTF8 (encodedTextBytes decomposedEncoded))
  assert (composedDecoded /= decomposedDecoded)
    "UTF-8 decoding normalized canonically equivalent Strings"

invalidUtf8Rejects :: Either String ()
invalidUtf8Rejects =
  mapM_ expectInvalid
    [ [0x80]
    , [0xc0, 0x80]
    , [0xe2, 0x82]
    , [0xed, 0xa0, 0x80]
    , [0xf4, 0x90, 0x80, 0x80]
    , [0xf5, 0x80, 0x80, 0x80]
    ]

exactBytesSubject :: Either String ()
exactBytesSubject = do
  source <- makeString [0x41, 0x03bb, 0x1f600]
  encoded <- mapLeft show (encodeText UTF8 source)
  assert
    (encodedTextBytesType encoded == TyBytes (RefNat 7))
    ("wrong exact Bytes subject: " <> show (encodedTextBytesType encoded))

correspondenceRejectsMismatch :: Either String ()
correspondenceRejectsMismatch = do
  source <- makeString [0x41]
  case checkTextEncodingCorrespondence UTF8 source [0x42] (TyBytes (RefNat 1)) of
    Left TextEncodingCorrespondenceMismatch -> Right ()
    other -> Left ("byte mismatch did not reject: " <> show other)
  case checkTextEncodingCorrespondence UTF8 source [0x41] (TyBytes (RefNat 2)) of
    Left TextEncodingCorrespondenceMismatch -> Right ()
    other -> Left ("subject mismatch did not reject: " <> show other)

noImplicitStringBytesConversion :: Either String ()
noImplicitStringBytesConversion = do
  let bytesType = TyBytes (RefNat 1)
  assert (unicodeStringCoreType /= bytesType)
    "String became definitionally equal to encoded Bytes"
  assert (compareTypes unicodeStringCoreType bytesType == IncompatibleTypes)
    "generic Core type comparison invented a String/Bytes conversion"

alternateEncodingSeparation :: Either String ()
alternateEncodingSeparation = do
  source <- makeString [0x41]
  case encodeText UTF16LE source of
    Left (TextEncodingUnsupported UTF16LE) -> Right ()
    other -> Left ("unsupported alternate encoding was not separated: " <> show other)
  case decodeText UTF16LE [0x41] of
    Left (TextEncodingUnsupported UTF16LE) -> Right ()
    other -> Left ("alternate decoding was silently treated as UTF-8: " <> show other)

expectInvalid :: [Word8] -> Either String ()
expectInvalid bytes = case decodeText UTF8 bytes of
  Left (TextDecodingInvalidUtf8 _) -> Right ()
  Left other -> Left ("wrong invalid UTF-8 diagnostic: " <> show other)
  Right value -> Left ("invalid UTF-8 decoded: " <> show (unicodeStringCodePoints value))

makeString :: [Integer] -> Either String UnicodeString
makeString codePoints = do
  scalars <- mapM (mapLeft show . unicodeScalar) codePoints
  Right (unicodeString scalars)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
