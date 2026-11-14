{-# LANGUAGE OverloadedStrings #-}

-- P8-C1: executed independent Unicode scalar / UTF-8 boundary controls.
-- This is NOT an accepted Haskell-to-Rocq proof or release capability.
module Main (main) where

import Control.Monad (unless)
import Data.Char (chr)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TE
import Phil.Core.Static (SemanticForm (..))
import Phil.Verification.P8SemanticFormCodec
  ( decodeP8SemanticForm, encodeP8SemanticForm )

check :: String -> Bool -> IO ()
check label ok = do
  unless ok (error ("P8-C1: " <> label))
  putStrLn ("P8-C1: " <> label)

isScalar :: Int -> Bool
isScalar n =
  n >= 0 && n <= 0x10ffff && (n < 0xd800 || n > 0xdfff)

-- Independently derived byte arithmetic. Comparing to Text.Encoding on
-- valid scalar inputs is an EXECUTED differential test, not a mechanized
-- semantic correspondence proof for the Haskell library.
referenceUtf8 :: Int -> BS.ByteString
referenceUtf8 n
  | n < 0x80 = BS.pack [fromIntegral n]
  | n < 0x800 = BS.pack
      [ fromIntegral (0xc0 + n `div` 64)
      , fromIntegral (0x80 + n `mod` 64) ]
  | n < 0x10000 = BS.pack
      [ fromIntegral (0xe0 + n `div` 4096)
      , fromIntegral (0x80 + (n `div` 64) `mod` 64)
      , fromIntegral (0x80 + n `mod` 64) ]
  | otherwise = BS.pack
      [ fromIntegral (0xf0 + n `div` 262144)
      , fromIntegral (0x80 + (n `div` 4096) `mod` 64)
      , fromIntegral (0x80 + (n `div` 64) `mod` 64)
      , fromIntegral (0x80 + n `mod` 64) ]

-- The existing codec frames atom text with the UTF-8 BYTE length.
atomWire :: BS.ByteString -> BS.ByteString
atomWire bytes =
  BS.concat ["at", BC.pack (show (BS.length bytes)), ":", bytes]

isRejected :: Either e a -> Bool
isRejected (Left _) = True
isRejected (Right _) = False

main :: IO ()
main = do
  let edges =
        [ 0, 1, 0x7f, 0x80, 0xbf, 0x7ff, 0x800, 0xd7ff
        , 0xe000, 0xffff, 0x10000, 0x1f642, 0x10ffff ]
      -- Repeatable, spread-out probes throughout the entire scalar domain.
      samples = filter isScalar (edges ++ [0, 127 .. 0x10ffff])
      correctScalar n =
        let value = Text.singleton (chr n)
            actual = TE.encodeUtf8 value
            diagnostic = encodeP8SemanticForm (SemanticAtom value)
        in actual == referenceUtf8 n
          && TE.decodeUtf8' actual == Right value
          && diagnostic == atomWire actual
          && decodeP8SemanticForm diagnostic == Right (SemanticAtom value)

  check "UTF-8 reference, native Text, and diagnostic codec agree at sampled scalar sites"
    (all correctScalar samples)
  check "scalar probes cover all widths and both Unicode extremes"
    (all (`elem` samples) [0, 0x7f, 0x80, 0x7ff, 0x800, 0x10000, 0x10ffff])
  check "surrogate scalars are not introduced as valid reference inputs"
    (all (not . isScalar) [0xd800, 0xdbff, 0xdc00, 0xdfff])

  let malformed =
        [ [0x80], [0xc0,0x80], [0xc1,0xbf], [0xe0,0x80,0x80]
        , [0xed,0xa0,0x80], [0xed,0xbf,0xbf]
        , [0xf0,0x80,0x80,0x80], [0xf4,0x90,0x80,0x80]
        , [0xf5,0x80,0x80,0x80], [0xe2,0x28,0xa1]
        , [0xf0,0x9f,0x99], [0xff], [0xc2] ]
      invalid bytes =
        isRejected (TE.decodeUtf8' (BS.pack bytes))
        && isRejected (decodeP8SemanticForm (atomWire (BS.pack bytes)))
  check "strict native Text decoder and existing codec reject malformed scalar bytes"
    (all invalid malformed)

  let composed = Text.singleton (chr 0xe9)
      decomposed = Text.pack ['e', chr 0x0301]
      nul = Text.pack ['x', '\0', 'y']
      sampleText = [composed, decomposed, nul, "ABC", "🙂", "é🙂\0x"]
  check "composed and decomposed Unicode remain distinct"
    (composed /= decomposed &&
     TE.encodeUtf8 composed /= TE.encodeUtf8 decomposed)
  check "byte-length framing roundtrips mixed multiscalar text without normalization"
    (all (\txt ->
      let actual = TE.encodeUtf8 txt
          wire = encodeP8SemanticForm (SemanticAtom txt)
      in wire == atomWire actual &&
         decodeP8SemanticForm wire == Right (SemanticAtom txt))
      sampleText)
  check "text frame rejects trailing bytes and noncanonical decimal count"
    (isRejected (decodeP8SemanticForm (atomWire "a" <> "junk"))
     && isRejected (decodeP8SemanticForm "at01:a"))
  putStrLn "P8-C1 native UTF-8 differential controls passed; no cross-language authority claimed"
