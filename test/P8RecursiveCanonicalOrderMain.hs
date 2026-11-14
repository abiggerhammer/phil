{-# LANGUAGE OverloadedStrings #-}

-- P8-C2 differential: actual native recursive Ord and diagnostic codec.
-- This is not a proved native-to-Rocq/accepted release mapping.
module Main (main) where

import Control.Monad (unless)
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.Encoding as TE
import Phil.Core.Generic
  ( GenericApplicationIdentity (..), GenericStaticParameterKey (..) )
import Phil.Core.Static
  ( DeclarationKey (..), InterfaceRevision (..), SemanticForm (..) )
import Phil.Verification.P8SemanticFormCodec
  ( encodeP8SemanticForm, decodeP8SemanticForm
  , encodeP8GenericApplication, decodeP8GenericApplication )

check :: String -> Bool -> IO ()
check label ok = do
  unless ok (error ("P8-C2: " <> label))
  putStrLn ("P8-C2: " <> label)

rejected :: Either e a -> Bool
rejected (Left _) = True
rejected (Right _) = False

rank :: SemanticForm -> Int
rank (SemanticAtom _) = 0
rank (SemanticOrdered _) = 1
rank (SemanticUnordered _) = 2
rank (SemanticRecord _) = 3

compareListBy :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
compareListBy _ [] [] = EQ
compareListBy _ [] (_ : _) = LT
compareListBy _ (_ : _) [] = GT
compareListBy cmp (x : xs) (y : ys) =
  case cmp x y of
    EQ -> compareListBy cmp xs ys
    result -> result

-- Reimplementation of structural comparison: never calls Ord SemanticForm.
compareFormReference :: SemanticForm -> SemanticForm -> Ordering
compareFormReference a b =
  case compare (rank a) (rank b) of
    EQ -> case (a, b) of
      (SemanticAtom x, SemanticAtom y) -> compare x y
      (SemanticOrdered xs, SemanticOrdered ys) ->
        compareListBy compareFormReference xs ys
      (SemanticUnordered xs, SemanticUnordered ys) ->
        compareListBy compareFormReference (Set.toAscList xs) (Set.toAscList ys)
      (SemanticRecord xs, SemanticRecord ys) ->
        compareListBy compareField
          (Map.toAscList xs) (Map.toAscList ys)
      _ -> error "P8-C2 impossible equal-rank constructor mismatch"
    unequal -> unequal
  where
    compareField (key1, value1) (key2, value2) =
      compare key1 key2 <> compareFormReference value1 value2

main :: IO ()
main = do
  let texts :: [Text]
      texts = ["", "a", "a\0", "b", "aa", "é", "e\x0301",
               "🙂", "é🙂", "\0", "Z", "\x10ffff"]
      leaves = map SemanticAtom texts ++
        [SemanticOrdered [], SemanticUnordered Set.empty,
         SemanticRecord Map.empty]
      pairs = [(a,b) | a <- take 7 leaves, b <- take 7 leaves]
      ordered = [SemanticOrdered [a,b] | (a,b) <- pairs]
      unordered = [SemanticUnordered (Set.fromList [a,b]) | (a,b) <- pairs]
      records = [SemanticRecord (Map.fromList [("a",a),("é",b)])
                | (a,b) <- pairs]
      nested = [SemanticOrdered
        [a, SemanticUnordered (Set.fromList [a,b]),
         SemanticRecord (Map.fromList [("🙂",b),("a",a)])]
        | (a,b) <- take 18 pairs]
      forms = leaves ++ ordered ++ unordered ++ records ++ nested
      wire = encodeP8SemanticForm

  check "all four recursive shapes and multilevel nested maps/sets roundtrip"
    (all (\form -> decodeP8SemanticForm (wire form) == Right form) forms)
  check "reference structural comparator agrees with actual native derived Ord"
    (and [compareFormReference a b == compare a b
         | a <- forms, b <- forms])
  check "diagnostic wire injective across distinct sampled forms"
    (Set.size (Set.fromList (map wire forms)) == Set.size (Set.fromList forms))
  check "native Unicode Text order agrees with UTF-8 octet lex for probes"
    (and [compare a b == compare (TE.encodeUtf8 a) (TE.encodeUtf8 b)
         | a <- texts, b <- texts])
  check "derived constructor rank differs from raw wire tag ordering"
    (let a = SemanticUnordered Set.empty
         b = SemanticRecord Map.empty
     in compare a b == LT && compare (wire a) (wire b) == GT)
  check "Set insertion duplicates normalize to the single accepted member"
    (wire (SemanticUnordered (Set.fromList
      [SemanticAtom "a",SemanticAtom "a"])) ==
     wire (SemanticUnordered (Set.fromList [SemanticAtom "a"])))
  check "Map insertion order cannot change canonical bytes"
    (wire (SemanticRecord (Map.fromList
      [("b",SemanticAtom "b"),("a",SemanticAtom "a")])) ==
     wire (SemanticRecord (Map.fromList
      [("a",SemanticAtom "a"),("b",SemanticAtom "b")])))
  check "reject duplicate or reverse-order set members"
    (all (rejected . decodeP8SemanticForm)
      ["u2:at1:aat1:a", "u2:at1:bat1:a"])
  check "reject duplicate or reverse-order record keys"
    (all (rejected . decodeP8SemanticForm)
      ["r2:t1:aat1:at1:aat1:b", "r2:t1:bat1:bt1:aat1:a"])
  check "reject malformed nested shape and surrogate UTF-8"
    (all (rejected . decodeP8SemanticForm)
      ["o2:at1:a", "at01:a", "o0:garbage",
       BS.concat ["at3:", BS.pack [0xed,0xa0,0x80]]])
  let app = GenericApplicationIdentity
        (DeclarationKey "same") (InterfaceRevision "same")
        (Map.fromList
          [ (GenericStaticParameterKey "a", SemanticAtom "same")
          , (GenericStaticParameterKey "b",
             SemanticOrdered [SemanticAtom "🙂",
               SemanticUnordered (Set.fromList [SemanticAtom "é"])] ) ])
      appWire = encodeP8GenericApplication app
      roleTamper = BS.take 1 appWire <> "V" <> BS.drop 2 appWire
  check "distinct D/V/Q/M role tags plus nested form generic roundtrip"
    (decodeP8GenericApplication appWire == Right app)
  check "wrong D role rejected despite same D/V payloads"
    (rejected (decodeP8GenericApplication roleTamper))
  check "duplicate and reverse-order generic Q keys rejected"
    (all (rejected . decodeP8GenericApplication)
      [ "gDt1:xVt1:y2:Qt1:aMat1:xQt1:aMat1:y"
      , "gDt1:xVt1:y2:Qt1:bMat1:xQt1:aMat1:y" ])
  putStrLn "P8-C2 native recursive order and canonical negatives passed"
