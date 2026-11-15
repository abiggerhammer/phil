{-# LANGUAGE OverloadedStrings #-}

-- P8-D1: strict native differential for arbitrary finite Unicode streams.
-- Finite executable probes are NOT a universal Haskell-to-Rocq theorem.
module Main (main) where

import Control.Monad (unless)
import Data.Char (chr)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TE
import Phil.Core.Static (SemanticForm (..))
import Phil.Verification.P8SemanticFormCodec
  (decodeP8SemanticForm, encodeP8SemanticForm)

check :: String -> Bool -> IO ()
check name ok = do
  unless ok (error ("P8-D1: " <> name))
  putStrLn ("P8-D1: " <> name)

isScalar :: Int -> Bool
isScalar n = n >= 0 && n <= 0x10ffff
  && (n < 0xd800 || n > 0xdfff)

referenceScalar :: Int -> BS.ByteString
referenceScalar n
  | n < 0x80 = BS.pack [fromIntegral n]
  | n < 0x800 = BS.pack
      [ fromIntegral (0xc0 + div n 64)
      , fromIntegral (0x80 + mod n 64) ]
  | n < 0x10000 = BS.pack
      [ fromIntegral (0xe0 + div n 4096)
      , fromIntegral (0x80 + mod (div n 64) 64)
      , fromIntegral (0x80 + mod n 64) ]
  | otherwise = BS.pack
      [ fromIntegral (0xf0 + div n 262144)
      , fromIntegral (0x80 + mod (div n 4096) 64)
      , fromIntegral (0x80 + mod (div n 64) 64)
      , fromIntegral (0x80 + mod n 64) ]

referenceStream :: [Int] -> BS.ByteString
referenceStream = BS.concat . map referenceScalar

textOf :: [Int] -> Text.Text
textOf = Text.pack . map chr

atomWire :: BS.ByteString -> BS.ByteString
atomWire bytes =
  BS.concat ["at", BC.pack (show (BS.length bytes)), ":", bytes]

isRejected :: Either e a -> Bool
isRejected (Left _) = True
isRejected (Right _) = False

isCorrect :: [Int] -> Bool
isCorrect xs =
  let txt = textOf xs
      actual = TE.encodeUtf8 txt
      wire = encodeP8SemanticForm (SemanticAtom txt)
  in all isScalar xs
    && actual == referenceStream xs
    && TE.decodeUtf8' actual == Right txt
    && wire == atomWire actual
    && decodeP8SemanticForm wire == Right (SemanticAtom txt)

main :: IO ()
main = do
  let boundaries =
        [0,1,0x7e,0x7f,0x80,0x81,0xbf,0xc0,0x7fe,0x7ff,0x800,0x801,
         0xd7fe,0xd7ff,0xe000,0xe001,0xfffe,0xffff,0x10000,0x10001,
         0x1f642,0x10fffe,0x10ffff,0x65,0xe9,0x301]
      spread = filter isScalar [0,127 .. 0x10ffff]
      adjacent = filter isScalar
        (concatMap (\n -> [n-2,n-1,n,n+1,n+2])
          [0,0x7f,0x80,0x7ff,0x800,0xd7ff,0xe000,0xffff,0x10000,0x10ffff])
      single = map (:[]) (filter isScalar (boundaries ++ spread ++ adjacent))
      multis =
        [ [], [0], [0,0,0], [0x65,0x301], [0xe9], [0xe9,0x1f642],
          [0x1f642,0,0x10ffff], [0x7f,0x80,0x7ff,0x800,0xd7ff,0xe000,0x10000],
          [0x10ffff,0x10ffff], [0x41,0xe9,0x42,0x1f642,0x43,0],
          [0x1f642,0x65,0x301,0xe9,0] ]
      pairs =
        [ [a,b] | a <- filter isScalar boundaries
                , b <- filter isScalar boundaries ]
      triples =
        [ [a,b,c] | a <- [0,0x7f,0x80,0x7ff,0x800,0xd7ff,
                           0xe000,0x10000,0x1f642,0x10ffff]
                  , b <- [0,0xe9,0x301,0x1f642]
                  , c <- [0,0x7f,0x800,0x10ffff] ]
      samples = single ++ multis ++ pairs ++ triples

  check "strict native UTF-8 agrees with independently calculated arbitrary streams"
    (all isCorrect samples)
  check "stream samples include empty, NUL, composed, decomposed and max scalar"
    (all (\xs -> elem xs samples) [[],[0],[0x65,0x301],[0xe9],
                                  [0x1f642,0,0x10ffff]])
  check "surrogate range is excluded from valid scalar generation"
    (all (not . isScalar) [0xd800,0xdbff,0xdc00,0xdfff])

  let malformed =
        [ [0x80], [0xbf], [0xc0,0x80], [0xc1,0xbf], [0xe0,0x80,0x80],
          [0xed,0xa0,0x80], [0xed,0xbf,0xbf],
          [0xf0,0x80,0x80,0x80], [0xf4,0x90,0x80,0x80],
          [0xf5,0x80,0x80,0x80], [0xe2,0x28,0xa1],
          [0xf0,0x9f,0x99], [0xff], [0xc2],
          [0x41,0xc2], [0x41,0xed,0xa0,0x80],
          [0xe9,0x41], [0x41,0x80], [0x41,0xf4,0x90,0x80,0x80],
          [0x41,0xe2,0x28,0xa1] ]
      invalid xs =
        let bytes = BS.pack xs
        in isRejected (TE.decodeUtf8' bytes)
          && isRejected (decodeP8SemanticForm (atomWire bytes))
  check "strict Text and diagnostic codec reject invalid middle/trailing streams"
    (all invalid malformed)

  let composed = textOf [0xe9]
      decomposed = textOf [0x65,0x301]
      withNul = textOf [0x65,0,0x301]
      multi = textOf [0,0xe9,0x1f642,0x10ffff]
      roundtrip txt =
        let b = TE.encodeUtf8 txt
        in decodeP8SemanticForm (atomWire b) == Right (SemanticAtom txt)
  check "canonical streams preserve composition and embedded NUL"
    (composed /= decomposed
      && TE.encodeUtf8 composed /= TE.encodeUtf8 decomposed
      && all roundtrip [composed,decomposed,withNul,multi,""])
  check "an extra valid scalar is valid text, but an extra byte breaks exact framing"
    (TE.decodeUtf8' (BS.pack [0,0]) == Right (textOf [0,0])
      && isRejected (decodeP8SemanticForm (atomWire "A" <> "B"))
      && isRejected (decodeP8SemanticForm "at01:A")
      && isRejected (decodeP8SemanticForm "at2:A"))
  putStrLn "P8-D1 native stream differential passed (no universal Text bridge claimed)"
