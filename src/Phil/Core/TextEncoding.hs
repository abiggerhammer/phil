module Phil.Core.TextEncoding
  ( TextEncoding (..)
  , TextEncodingError (..)
  , EncodedText
  , encodedTextEncoding
  , encodedTextSource
  , encodedTextBytes
  , encodedTextBytesType
  , encodeText
  , decodeText
  , checkEncodedTextCorrespondence
  ) where

import Data.Bits
  ( (.&.)
  , (.|.)
  , shiftR
  , shiftL
  )
import Data.Word (Word8)
import Phil.Core.Syntax
  ( RefTerm (..)
  , Ty (..)
  )
import Phil.Core.UnicodeChar
  ( UnicodeCharError
  , UnicodeScalar
  , unicodeScalar
  )
import Phil.Core.UnicodeString
  ( UnicodeString
  , unicodeString
  , unicodeStringCodePoints
  )

-- | Encoding selection is semantic and explicit. UTF16LE is named here only to
-- demonstrate that encoding identity is part of the contract; Phase 1 initially
-- implements UTF-8 only.
data TextEncoding
  = UTF8
  | UTF16LE
  deriving (Eq, Ord, Show)

data TextEncodingError
  = TextEncodingUnsupported TextEncoding
  | TextDecodingInvalidUtf8 Int
  | TextDecodingScalarError Int UnicodeCharError
  | TextEncodingCorrespondenceMismatch
  deriving (Eq, Show)

-- | Exact correspondence witness between one Phil String and one encoded byte
-- subject. The constructor is hidden so callers cannot relabel arbitrary bytes
-- as an encoding result.
data EncodedText = EncodedText
  { encodedTextEncoding :: TextEncoding
  , encodedTextSource :: UnicodeString
  , encodedTextBytes :: [Word8]
  , encodedTextBytesType :: Ty
  }
  deriving (Eq, Show)

encodeText
  :: TextEncoding
  -> UnicodeString
  -> Either TextEncodingError EncodedText
encodeText encoding source = case encoding of
  UTF8 ->
    let bytes = concatMap encodeUtf8Scalar (unicodeStringCodePoints source)
    in Right EncodedText
      { encodedTextEncoding = UTF8
      , encodedTextSource = source
      , encodedTextBytes = bytes
      , encodedTextBytesType = TyBytes (RefNat (toInteger (length bytes)))
      }
  unsupported -> Left (TextEncodingUnsupported unsupported)

decodeText
  :: TextEncoding
  -> [Word8]
  -> Either TextEncodingError UnicodeString
decodeText encoding bytes = case encoding of
  UTF8 -> unicodeString <$> decodeUtf8 bytes
  unsupported -> Left (TextEncodingUnsupported unsupported)

checkEncodedTextCorrespondence
  :: EncodedText
  -> Either TextEncodingError ()
checkEncodedTextCorrespondence witness = do
  expected <- encodeText
    (encodedTextEncoding witness)
    (encodedTextSource witness)
  if encodedTextBytes witness == encodedTextBytes expected
      && encodedTextBytesType witness == encodedTextBytesType expected
    then Right ()
    else Left TextEncodingCorrespondenceMismatch

encodeUtf8Scalar :: Integer -> [Word8]
encodeUtf8Scalar codePoint
  | codePoint <= 0x7f =
      [fromInteger codePoint]
  | codePoint <= 0x7ff =
      [ fromInteger (0xc0 .|. shiftR codePoint 6)
      , fromInteger (0x80 .|. (codePoint .&. 0x3f))
      ]
  | codePoint <= 0xffff =
      [ fromInteger (0xe0 .|. shiftR codePoint 12)
      , fromInteger (0x80 .|. (shiftR codePoint 6 .&. 0x3f))
      , fromInteger (0x80 .|. (codePoint .&. 0x3f))
      ]
  | otherwise =
      [ fromInteger (0xf0 .|. shiftR codePoint 18)
      , fromInteger (0x80 .|. (shiftR codePoint 12 .&. 0x3f))
      , fromInteger (0x80 .|. (shiftR codePoint 6 .&. 0x3f))
      , fromInteger (0x80 .|. (codePoint .&. 0x3f))
      ]

decodeUtf8 :: [Word8] -> Either TextEncodingError [UnicodeScalar]
decodeUtf8 = go 0
  where
    go _ [] = Right []
    go offset remaining = do
      (codePoint, width) <- decodeOne offset remaining
      scalar <- mapLeft (TextDecodingScalarError offset) (unicodeScalar codePoint)
      rest <- go (offset + width) (drop width remaining)
      Right (scalar : rest)

decodeOne :: Int -> [Word8] -> Either TextEncodingError (Integer, Int)
decodeOne offset bytes = case bytes of
  b0 : _
    | b0 <= 0x7f -> Right (toInteger b0, 1)
    | b0 >= 0xc2 && b0 <= 0xdf -> do
        b1 <- requireContinuation offset 1 bytes
        Right
          ( shiftL (toInteger (b0 .&. 0x1f)) 6
              .|. toInteger (b1 .&. 0x3f)
          , 2
          )
    | b0 >= 0xe0 && b0 <= 0xef -> do
        b1 <- requireContinuation offset 1 bytes
        b2 <- requireContinuation offset 2 bytes
        if validThreeByteSecond b0 b1
          then Right
            ( shiftL (toInteger (b0 .&. 0x0f)) 12
                .|. shiftL (toInteger (b1 .&. 0x3f)) 6
                .|. toInteger (b2 .&. 0x3f)
            , 3
            )
          else Left (TextDecodingInvalidUtf8 offset)
    | b0 >= 0xf0 && b0 <= 0xf4 -> do
        b1 <- requireContinuation offset 1 bytes
        b2 <- requireContinuation offset 2 bytes
        b3 <- requireContinuation offset 3 bytes
        if validFourByteSecond b0 b1
          then Right
            ( shiftL (toInteger (b0 .&. 0x07)) 18
                .|. shiftL (toInteger (b1 .&. 0x3f)) 12
                .|. shiftL (toInteger (b2 .&. 0x3f)) 6
                .|. toInteger (b3 .&. 0x3f)
            , 4
            )
          else Left (TextDecodingInvalidUtf8 offset)
    | otherwise -> Left (TextDecodingInvalidUtf8 offset)
  [] -> Left (TextDecodingInvalidUtf8 offset)

requireContinuation
  :: Int
  -> Int
  -> [Word8]
  -> Either TextEncodingError Word8
requireContinuation offset relative bytes =
  case drop relative bytes of
    value : _
      | value >= 0x80 && value <= 0xbf -> Right value
    _ -> Left (TextDecodingInvalidUtf8 offset)

validThreeByteSecond :: Word8 -> Word8 -> Bool
validThreeByteSecond first second
  | first == 0xe0 = second >= 0xa0 && second <= 0xbf
  | first == 0xed = second >= 0x80 && second <= 0x9f
  | otherwise = second >= 0x80 && second <= 0xbf

validFourByteSecond :: Word8 -> Word8 -> Bool
validFourByteSecond first second
  | first == 0xf0 = second >= 0x90 && second <= 0xbf
  | first == 0xf4 = second >= 0x80 && second <= 0x8f
  | otherwise = second >= 0x80 && second <= 0xbf

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
