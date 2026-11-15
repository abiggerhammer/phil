{-# LANGUAGE OverloadedStrings #-}

-- P8-E2 independent native differential, NOT universal Haskell/Rocq proof.
module Main (main) where

import Control.Monad (unless)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TE
import Phil.Core.Generic (GenericApplicationIdentity (..), GenericStaticParameterKey (..))
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..), SemanticForm (..))
import Phil.Verification.P8SemanticFormCodec
  ( encodeP8SemanticForm, decodeP8SemanticForm
  , encodeP8GenericApplication, decodeP8GenericApplication )

check :: String -> Bool -> IO ()
check label yes = do
  unless yes (error ("P8-E2 FAIL: " <> label))
  putStrLn ("P8-E2 PASS: " <> label)

rejected :: Either e a -> Bool
rejected (Left _) = True
rejected (Right _) = False

mkApplication :: Text -> Text -> [(Text, SemanticForm)] -> GenericApplicationIdentity
mkApplication declaration revision fields =
  GenericApplicationIdentity
    (DeclarationKey declaration)
    (InterfaceRevision revision)
    (Map.fromList [(GenericStaticParameterKey key, value) | (key, value) <- fields])

putText :: Text -> BS.ByteString
putText value =
  let raw = TE.encodeUtf8 value
  in BS.concat ["t", BSC.pack (show (BS.length raw)), ":", raw]

main :: IO ()
main = do
  let accent = "\x00e9" :: Text
      decomp = "e\x0301" :: Text
      smile = "\x1f642" :: Text
      maximumScalar = "\x10ffff" :: Text
      boundaryPayloads = ["", "\0", accent, decomp, smile, maximumScalar,
                          "A\0B", "\0" <> accent <> smile, Text.replicate 100 accent]
      atoms = map SemanticAtom boundaryPayloads
      tinySet = SemanticUnordered (Set.fromList
        [SemanticAtom "\0", SemanticAtom accent, SemanticRecord Map.empty])
      tinyRecord = SemanticRecord (Map.fromList
        [("a", tinySet), (smile, SemanticOrdered atoms)])
      nested = SemanticOrdered
        [SemanticAtom decomp, tinySet, tinyRecord, SemanticOrdered []]
      examples = atoms ++
        [SemanticOrdered [], SemanticUnordered Set.empty,
         SemanticRecord Map.empty, tinySet, tinyRecord, nested]
      encodeForm = encodeP8SemanticForm
      decodeForm = decodeP8SemanticForm
      encodeApp = encodeP8GenericApplication
      decodeApp = decodeP8GenericApplication
      emptyApp = mkApplication "" "" []
      sameBytes = mkApplication "x" "x" [("x", SemanticAtom "x")]
      application = mkApplication ("\0" <> smile) accent
        [ ("z", tinyRecord)
        , ("\0", SemanticAtom maximumScalar)
        , (smile, nested)
        , (accent, SemanticUnordered (Set.fromList
            [SemanticRecord Map.empty, SemanticUnordered Set.empty])) ]
      apps = [emptyApp, sameBytes, application,
              mkApplication decomp maximumScalar
                [(accent, SemanticAtom decomp), (decomp, SemanticAtom accent)]]

  check "real native four-constructors deeply nested diagnostic roundtrip"
    (all (\x -> decodeForm (encodeForm x) == Right x) examples)
  check "all native text lengths are real UTF8 byte lengths"
    (all (\x -> encodeForm (SemanticAtom x) == BS.cons 97 (putText x))
      boundaryPayloads)
  check "real native derived Ord differs from tag byte order"
    (let u = SemanticUnordered Set.empty
         r = SemanticRecord Map.empty
     in u < r && encodeForm u > encodeForm r)
  check "native semantic-form and parameter Map/Set canonicalization"
    (encodeForm (SemanticUnordered (Set.fromList
        [SemanticAtom "b", SemanticAtom "a", SemanticAtom "a"]))
      == "u2:at1:aat1:b" &&
     encodeForm (SemanticRecord (Map.fromList
        [("b", SemanticAtom "b"), ("a", SemanticAtom "a")]))
      == "r2:t1:aat1:at1:bat1:b")

  check "native typed GenericApplication full roundtrip"
    (all (\x -> decodeApp (encodeApp x) == Right x) apps)
  check "empty app has explicit D V roles and zero arity"
    (encodeApp emptyApp == "gDt0:Vt0:0:")
  check "same UTF8 bytes remain distinct D V Q M roles"
    (encodeApp sameBytes == "gDt1:xVt1:x1:Qt1:xMat1:x")
  check "application uses actual sorted native Map keys"
    (encodeApp (mkApplication "a" "b"
       [("z", SemanticAtom "1"), ("a", SemanticAtom "2")])
     == "gDt1:aVt1:b2:Qt1:aMat1:2Qt1:zMat1:1")
  check "application strict supplementary Unicode byte count"
    (BS.isInfixOf (BS.concat ["Dt5:", TE.encodeUtf8 ("\0" <> smile)])
      (encodeApp application))

  let malformedForms =
        [ "at01:a", "at2:a", "at1:aa", "at0:garbage"
        , "o2:at0:", "o1:at0:at0:", "o00:", "r01:t0:at0:"
        , "u2:at1:aat1:a", "u2:at1:bat1:a"
        , "r2:t1:aat0:t1:aat0:", "r2:t1:bat0:t1:aat0:"
        , "r1:t1:ao2:at0:", "z0:", "u0:garbage"
        , "o999999999999999999999999999999999:"
        ]
      malformedApps =
        [ "gDt0:Vt0:0:tail"
        , "gVt0:Dt0:0:", "gDt0:Dt0:0:", "gDt0:Qt0:0:"
        , "gDt0:Vt0:00:", "gDt0:Vt0:01:Qt0:Mat0:"
        , "gDt0:Vt0:1:Mt1:xQat0:"
        , "gDt0:Vt0:1:Qt1:xQat0:"
        , "gDt0:Vt0:1:Qt1:xMat0:trailing"
        , "gDt0:Vt0:1:Qt1:xM"
        , "gDt0:Vt0:2:Qt1:aMat0:Qt1:aMat0:"
        , "gDt0:Vt0:2:Qt1:bMat0:Qt1:aMat0:"
        , "gDt0:Vt0:1:Qt2:aMat0:"
        , "gDt0:Vt0:2:Qt1:aMat0:"
        , "gDt0:Vt0:9999999999999999999999:"
        , "gDt0:Vt0:1:Qt1:xMat2:a"
        ]
      invalidUtf8 =
        [ [255], [128], [192,128], [224,128,128]
        , [237,160,128], [244,144,128,128], [240,159,153]
        , [195,40], [0,237,160,128] ]
  check "native rejects malformed recursive structural forms"
    (all (rejected . decodeForm) malformedForms)
  check "native rejects role swaps, omitted role, forged count, duplicated Q"
    (all (rejected . decodeApp) malformedApps)
  check "native rejects malformed UTF8 in selected declaration and Q key"
    (and [ let raw = BS.pack xs
               len = BSC.pack (show (BS.length raw))
           in rejected (decodeApp (BS.concat
                ["gDt", len, ":", raw, "Vt0:0:"]))
              && rejected (decodeApp (BS.concat
                ["gDt0:Vt0:1:Qt", len, ":", raw, "Mat0:"]))
         | xs <- invalidUtf8 ])
  check "native rejects noncanonical UTF8 nested application values"
    (all (rejected . decodeApp)
      [ "gDt0:Vt0:1:Qt1:xMat2:\xc0\x80"
      , "gDt0:Vt0:1:Qt1:xMo1:at2:\xed\xa0\x80"
      , "gDt0:Vt0:1:Qt1:xMu2:at1:aat1:a"
      , "gDt0:Vt0:1:Qt1:xMr2:t1:aat0:t1:aat0:" ])
  putStrLn "P8-E2 actual Haskell recursive and typed-application tests complete"
