{-# LANGUAGE OverloadedStrings #-}

-- Real native diagnostic-codec differential; not an operational-semantic proof.
module Main (main) where

import Control.Monad (unless)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TE
import Phil.Core.Static (SemanticForm (..))
import Phil.Verification.P8SemanticFormCodec
  ( encodeP8SemanticForm, decodeP8SemanticForm )

check :: String -> Bool -> IO ()
check label yes = do
  unless yes (error ("P8-E1 FAIL: " <> label))
  putStrLn ("P8-E1 PASS: " <> label)

rejected :: Either e a -> Bool
rejected (Left _) = True
rejected (Right _) = False

textWire :: Text -> BS.ByteString
textWire t =
  let bytes = TE.encodeUtf8 t
  in BS.concat ["t", BSC.pack (show (BS.length bytes)), ":", bytes]

main :: IO ()
main = do
  let accent = "\x00e9" :: Text
      decomposed = "e\x0301" :: Text
      smile = "\x1f642" :: Text
      maxScalar = "\x10ffff" :: Text
      payloads = ["", "\0", "A", accent, decomposed, smile,
                  maxScalar, "\0" <> accent <> smile, "a\0b", "\0\0"]
      atoms = map SemanticAtom payloads
      emptyOrdered = SemanticOrdered []
      emptySet = SemanticUnordered Set.empty
      emptyRecord = SemanticRecord Map.empty
      nested = SemanticRecord (Map.fromList
        [ ("\0", SemanticOrdered
           [ SemanticAtom ("\0" <> smile)
           , SemanticUnordered (Set.fromList
                [SemanticAtom "a", SemanticAtom accent]) ])
        , (smile, SemanticRecord (Map.fromList
            [(accent, SemanticAtom decomposed)])) ])
      forms = atoms ++ [emptyOrdered, emptySet, emptyRecord,
                       SemanticOrdered atoms, nested]
      wire = encodeP8SemanticForm
      parse = decodeP8SemanticForm

  check "real native UTF8 byte lengths, not Text character counts"
    (all (\t -> wire (SemanticAtom t) == BS.cons 97 (textWire t)) payloads)
  check "every native canonical example decodes without trimming"
    (all (\form -> parse (wire form) == Right form) forms)
  check "empty four-constructor encodings are distinct"
    (map wire [SemanticAtom "", emptyOrdered, emptySet, emptyRecord]
        == ["at0:", "o0:", "u0:", "r0:"])
  check "multidigit length is byte-counted exactly"
    (wire (SemanticAtom (Text.replicate 100 "é"))
      == BS.concat ["at200:", TE.encodeUtf8 (Text.replicate 100 "é")])
  check "composed and decomposed are not normalized"
    (wire (SemanticAtom accent) /= wire (SemanticAtom decomposed))
  check "native constructor Ord is not wire lexicographic order"
    (let u = SemanticUnordered Set.empty
         r = SemanticRecord Map.empty
     in u < r && wire u > wire r)
  check "native Set and Map input order is canonical on the wire"
    (wire (SemanticUnordered (Set.fromList
      [SemanticAtom "b", SemanticAtom "a", SemanticAtom "a"]))
       == "u2:at1:aat1:b"
      && wire (SemanticRecord (Map.fromList
        [("b",SemanticAtom "b"),("a",SemanticAtom "a")]))
       == "r2:t1:aat1:at1:bat1:b")

  let malformed =
        [ "at00:", "at01:a", "at-1:a", "at+1:a", "at1", "at1a", "at:a"
        , "at2:a", "at1:ab", "at0:extra", "at1:a\0"
        , "o00:", "o01:at0:", "o2:at0:", "o1:at0:at0:"
        , "u2:at1:aat1:a", "u2:at1:bat1:a"
        , "r2:t1:aat0:t1:aat0:", "r2:t1:bat0:t1:aat0:"
        , "r1:t1:aat0:garbage", "r1:t2:a", "r1:at0:"
        , "z0:", "o0:trailing", "u0:trailing", "r0:trailing"
        , "o9999999999999999999999999:"
        ]
      invalidUtf8 =
        [ [255], [128], [192,128], [224,128,128], [237,160,128]
        , [244,144,128,128], [240,159,153], [195,40]
        , [97,255], [0,237,160,128] ]
  check "native rejects every truncated, forged or noncanonical frame"
    (all (rejected . parse) malformed)
  check "native rejects strict invalid UTF8 in atoms and record keys"
    (and [ rejected (parse (BS.concat
              ["at", BSC.pack (show (length bytes)), ":", BS.pack bytes]))
         && rejected (parse (BS.concat
              ["r1:t", BSC.pack (show (length bytes)), ":",
               BS.pack bytes, "at0:"]))
         | bytes <- invalidUtf8 ])
  check "native rejects recursive count and duplicate-member tampering"
    (all (rejected . parse)
      [ "o1:u2:at1:aat1:a"
      , "o1:r2:t1:aat0:t1:aat0:"
      , "o2:at1:a"
      , "r1:t1:ao2:at0:" ])
  putStrLn "P8-E1 real native diagnostic-codec differential complete"
