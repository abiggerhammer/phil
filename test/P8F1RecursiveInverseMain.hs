{-# LANGUAGE OverloadedStrings #-}

-- P8-F1: independent native diagnostic regression; samples are not a
-- proof of all GHC Text, Ord, Map and Set operational semantics.
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
check name ok = do
  unless ok (error ("P8-F1 FAILED: " <> name))
  putStrLn ("P8-F1 PASS: " <> name)

rejected :: Either e a -> Bool
rejected (Left _) = True
rejected (Right _) = False

makeApp :: Text -> Text -> [(Text, SemanticForm)] -> GenericApplicationIdentity
makeApp declaration revision args =
  GenericApplicationIdentity (DeclarationKey declaration) (InterfaceRevision revision)
    (Map.fromList [(GenericStaticParameterKey key, value) | (key, value) <- args])

nest :: Int -> SemanticForm -> SemanticForm
nest depth value =
  foldr (\_ x -> SemanticOrdered [x]) value [1..depth]

main :: IO ()
main = do
  let texts = ["", "\0", "\x00e9", "e\x0301", "\x1f642",
               "\x10ffff", "a\0b", "z\x00e9\x1f642"]
      atoms = map SemanticAtom texts
      samples =
        atoms
        ++ [SemanticOrdered [], SemanticUnordered Set.empty, SemanticRecord Map.empty]
        ++ map (\n -> nest n (SemanticAtom "\0\x00e9\x1f642")) [0, 1, 2, 5, 16, 64]
        ++ [SemanticOrdered (take n (cycle atoms)) | n <- [0, 1, 9, 10, 99, 100]]
        ++ [SemanticUnordered (Set.fromList (take n (cycle atoms)))
            | n <- [0, 1, 2, 8, 100]]
        ++ [SemanticRecord (Map.fromList (zip
              (map (Text.pack . show) [0 :: Int .. n]) (cycle atoms)))
            | n <- [0, 1, 9, 10, 99, 100]]
      app = makeApp "\0\x1f642" "\x00e9"
        [("z", nest 16 (SemanticAtom "e\x0301")),
         ("\0", SemanticUnordered (Set.fromList atoms)),
         ("\x1f642", SemanticRecord (Map.fromList
           [("\x00e9", SemanticAtom "\0"), ("a", SemanticOrdered atoms)]))]
      apps = [makeApp "" "" [], makeApp "x" "x" [("x", SemanticAtom "x")], app]
      nativeLength txt =
        let bs = TE.encodeUtf8 txt
        in BS.concat ["at", BSC.pack (show (BS.length bs)), ":", bs]

  check "all four native constructors and unbounded finite nesting"
    (all (\f -> decodeP8SemanticForm (encodeP8SemanticForm f) == Right f) samples)
  check "strict native Unicode framing uses octets, never character count"
    (all (\t -> encodeP8SemanticForm (SemanticAtom t) == nativeLength t) texts)
  check "composed and decomposed Unicode remain distinct"
    (encodeP8SemanticForm (SemanticAtom "\x00e9")
      /= encodeP8SemanticForm (SemanticAtom "e\x0301"))
  check "actual native Set/Map normalization and derived Ord"
    (let u = SemanticUnordered (Set.fromList [SemanticAtom "\x00e9",
                                               SemanticAtom "\0", SemanticAtom "\0"])
         r = SemanticRecord (Map.fromList [("b", u), ("a", SemanticAtom "\x1f642")])
     in u < r &&
        decodeP8SemanticForm (encodeP8SemanticForm r) == Right r)
  check "typed D V Q M native application differential"
    (all (\a -> decodeP8GenericApplication (encodeP8GenericApplication a) == Right a)
       apps)
  check "canonical decimal lengths including base-ten boundaries"
    (all (\n -> let t = Text.replicate n "x"
                in encodeP8SemanticForm (SemanticAtom t) ==
                   BS.concat ["at", BSC.pack (show n), ":", TE.encodeUtf8 t])
       [0, 1, 9, 10, 99, 100, 999, 1000])
  check "reject noncanonical lengths counts and nested/trailing forms"
    (all (rejected . decodeP8SemanticForm)
       ["at00:", "at01:a", "at2:a", "at0:garbage",
        "o01:at0:", "o2:at0:", "o1:at0:at0:",
        "r2:t1:bat0:t1:aat0:",
        "u2:at1:aat1:a", "u2:at1:bat1:a",
        "u1:at1:a\0", "r1:t1:xat2:a",
        "at2:\xc0\x80", "at3:\xed\xa0\x80", "at4:\xf4\x90\x80\x80"])
  check "reject forged D V Q M role, duplicate Q and truncated application"
    (all (rejected . decodeP8GenericApplication)
       ["gVt0:Dt0:0:", "gDt0:Dt0:0:", "gDt0:Vt0:01:",
        "gDt0:Vt0:1:Mt1:xQat0:",
        "gDt0:Vt0:1:Qt1:xQat0:",
        "gDt0:Vt0:2:Qt1:xMat0:Qt1:xMat0:",
        "gDt0:Vt0:1:Qt1:xMat2:a",
        "gDt0:Vt0:0:trailing"])
  putStrLn "P8-F1 diagnostic native differential complete"
