{-# LANGUAGE OverloadedStrings #-}

-- Executable P8 data-level controls; never an accepted release certificate.
module Main (main) where

import Control.Monad (unless)
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Generic
  ( GenericApplicationIdentity (..), GenericStaticParameterKey (..)
  , deriveGenericApplicationIdentity )
import Phil.Core.Static
  ( DeclarationKey (..), InterfaceRevision (..), SemanticForm (..) )
import Phil.Verification.P8SemanticFormCodec
  ( encodeP8SemanticForm, decodeP8SemanticForm
  , encodeP8GenericApplication, decodeP8GenericApplication )

check :: String -> Bool -> IO ()
check label yes = do
  unless yes (error ("P8 codec: " <> label))
  putStrLn ("P8 codec check: " <> label)

rejected :: Either String a -> Bool
rejected (Left _) = True
rejected (Right _) = False

main :: IO ()
main = do
  let accent = Text.singleton '\x00E9'
      smile = Text.singleton '\x1F642'
      nul = Text.pack ['x','\0','y']
      decomposed = Text.pack ['e','\x0301']
      atom = SemanticAtom
      complex = SemanticRecord (Map.fromList
        [ ("nested", SemanticOrdered
            [atom accent, SemanticUnordered (Set.fromList [atom smile, atom nul])])
        , (smile, SemanticRecord (Map.fromList [(nul, atom decomposed)]))
        , ("empty", SemanticUnordered Set.empty)
        ])
      forms = [atom "",atom accent,atom smile,atom nul,atom decomposed,
               SemanticOrdered [],SemanticOrdered [atom "b",complex,atom "a"],
               SemanticUnordered Set.empty,
               SemanticUnordered (Set.fromList [atom smile,atom accent,complex]),
               SemanticRecord Map.empty,complex]
      wire = encodeP8SemanticForm
      decode = decodeP8SemanticForm

  check "all native recursive constructors, Unicode and NUL roundtrip"
    (all (\x -> decode (wire x) == Right x) forms)
  check "composed/decomposed remain distinguished"
    (wire (atom accent) /= wire (atom decomposed))
  check "UTF-8 byte count differs from Unicode text length"
    (BS.length (wire (atom smile)) > BS.length (wire (atom "a")))
  check "native Set insertion order and dedup canonical"
    (wire (SemanticUnordered (Set.fromList [atom "b",atom "a",atom "a"]))
      == wire (SemanticUnordered (Set.fromList [atom "a",atom "b"])))
  check "native Map insertion order canonical"
    (wire (SemanticRecord (Map.fromList [("b",atom "b"),("a",atom "a")]))
      == wire (SemanticRecord (Map.fromList [("a",atom "a"),("b",atom "b")])))
  check "ordered child order observable"
    (wire (SemanticOrdered [atom "a",atom "b"]) /=
     wire (SemanticOrdered [atom "b",atom "a"]))
  check "empty constructors distinct"
    (Set.size (Set.fromList
      (map wire [atom "",SemanticOrdered [],SemanticUnordered Set.empty,
                 SemanticRecord Map.empty])) == 4)
  check "sampled native form encoding is injective"
    (Set.size (Set.fromList (map wire forms)) == Set.size (Set.fromList forms))
  check "reject invalid UTF-8" (rejected (decode (BS.pack [97,116,49,58,255])))
  check "reject truncated UTF-8" (rejected (decode (BS.pack [97,116,49,58,195])))
  check "reject leading-zero byte length" (rejected (decode "at01:a"))
  check "reject bad decimal byte length" (rejected (decode "atx:a"))
  check "reject exaggerated byte length" (rejected (decode "at2:a"))
  check "reject trailing data" (rejected (decode (wire (atom "a") <> "junk")))
  check "reject unsorted set" (rejected (decode "u2:at1:bat1:a"))
  check "reject duplicated set member" (rejected (decode "u2:at1:aat1:a"))
  check "reject unsorted record keys"
    (rejected (decode "r2:t1:bat1:bt1:aat1:a"))
  check "reject duplicate record keys"
    (rejected (decode "r2:t1:aat1:bt1:aat1:a"))
  check "reject impossible child count" (rejected (decode "o99999999999:"))
  check "reject unexpected constructor tag" (rejected (decode "zt1:a"))

  let d = DeclarationKey "source"
      v = InterfaceRevision (Text.pack ['v','\0','r'])
      qa = GenericStaticParameterKey "alpha"
      qz = GenericStaticParameterKey smile
  case deriveGenericApplicationIdentity d v [(qz,complex),(qa,atom accent)] of
    Left e -> error ("genuine native generic identity derivation failed: " <> show e)
    Right app -> do
      let canonical = GenericApplicationIdentity d v
            (Map.fromList [(qa,atom accent),(qz,complex)])
          changed = GenericApplicationIdentity d v
            (Map.fromList [(qa,atom decomposed),(qz,complex)])
          encodeApp = encodeP8GenericApplication
      check "actual native generic D/V/Q/M roundtrip"
        (decodeP8GenericApplication (encodeApp app) == Right app)
      check "generic argument order canonical"
        (encodeApp app == encodeApp canonical)
      check "same Q with distinct M cannot serialize equally"
        (encodeApp app /= encodeApp changed)
      check "form and generic role domains separate"
        (rejected (decode (encodeApp app))
         && rejected (decodeP8GenericApplication (wire complex)))
      check "native identity producer rejects duplicate Q domain"
        (rejected (deriveGenericApplicationIdentity d v
          [(qa,atom "x"),(qa,atom "y")]))

  check "reject D/V role swap" (rejected
    (decodeP8GenericApplication "gVt1:dDt1:v0:"))
  check "reject Q/M role swap" (rejected
    (decodeP8GenericApplication "gDt1:dVt1:v1:Mt1:qQat1:x"))
  check "reject repeated generic Q keys" (rejected
    (decodeP8GenericApplication "gDt1:dVt1:v2:Qt1:qMat1:xQt1:qMat1:y"))
  check "reject out-of-order generic Q keys" (rejected
    (decodeP8GenericApplication "gDt1:dVt1:v2:Qt1:zMat1:xQt1:aMat1:y"))
  check "reject non-UTF8 generic D" (rejected
    (decodeP8GenericApplication (BS.pack
      [103,68,116,49,58,255,86,116,49,58,118,48,58])))

  putStrLn "P8 native candidate roundtrip and adversarial checks passed; no authority claim"
