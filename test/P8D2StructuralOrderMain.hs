{-# LANGUAGE OverloadedStrings #-}

-- P8-D2 native differential against *real* Phil.Core.Static, Generic
-- and the existing diagnostic codec.  It is not a universal operational
-- semantics proof nor a final authority accepting path.
module Main (main) where

import Control.Monad (unless)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.List (sortBy)
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
check msg result = do
  unless result (error ("P8-D2 failure: " <> msg))
  putStrLn ("P8-D2 PASS: " <> msg)

rejected :: Either e a -> Bool
rejected (Left _) = True
rejected (Right _) = False

rank :: SemanticForm -> Int
rank (SemanticAtom _) = 0
rank (SemanticOrdered _) = 1
rank (SemanticUnordered _) = 2
rank (SemanticRecord _) = 3

compareTextBytes :: Text -> Text -> Ordering
compareTextBytes x y = compare (TE.encodeUtf8 x) (TE.encodeUtf8 y)

compareListBy :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
compareListBy _ [] [] = EQ
compareListBy _ [] (_ : _) = LT
compareListBy _ (_ : _) [] = GT
compareListBy cmp (x : xs) (y : ys) =
  case cmp x y of
    EQ -> compareListBy cmp xs ys
    other -> other

compareFormRef :: SemanticForm -> SemanticForm -> Ordering
compareFormRef left right =
  case compare (rank left) (rank right) of
    EQ -> case (left, right) of
      (SemanticAtom x, SemanticAtom y) -> compareTextBytes x y
      (SemanticOrdered xs, SemanticOrdered ys) ->
        compareListBy compareFormRef xs ys
      (SemanticUnordered xs, SemanticUnordered ys) ->
        compareListBy compareFormRef (sortBy compareFormRef (Set.toList xs))
          (sortBy compareFormRef (Set.toList ys))
      (SemanticRecord xs, SemanticRecord ys) ->
        compareListBy compareField
          (sortBy compareKey (Map.toList xs))
          (sortBy compareKey (Map.toList ys))
      _ -> error "impossible equal-rank SemanticForm mismatch"
    other -> other
  where
    compareKey (x, _) (y, _) = compareTextBytes x y
    compareField (key, a) (otherKey, b) =
      compareTextBytes key otherKey <> compareFormRef a b

encodeTextRef :: Text -> BS.ByteString
encodeTextRef txt =
  let bs = TE.encodeUtf8 txt
  in BS.concat ["t", BSC.pack (show (BS.length bs)), ":", bs]

encodeFormRef :: SemanticForm -> BS.ByteString
encodeFormRef form = case form of
  SemanticAtom txt -> BS.cons 97 (encodeTextRef txt)
  SemanticOrdered xs ->
    BS.concat (["o", BSC.pack (show (length xs)), ":"] ++ map encodeFormRef xs)
  SemanticUnordered xs ->
    let ordered = sortBy compareFormRef (Set.toList xs)
    in BS.concat (["u", BSC.pack (show (length ordered)), ":"]
      ++ map encodeFormRef ordered)
  SemanticRecord xs ->
    let ordered = sortBy (\(a, _) (b, _) -> compareTextBytes a b)
          (Map.toList xs)
    in BS.concat (["r", BSC.pack (show (length ordered)), ":"]
      ++ concatMap (\(k, v) -> [encodeTextRef k, encodeFormRef v]) ordered)

main :: IO ()
main = do
  let unicode :: [Text]
      unicode = ["", "\0", "a", "ab", "é", "e\x0301", "🙂",
                 "🙂é", "\x10ffff", "z\0é", "\0🙂", "a\0b"]
      atoms = map SemanticAtom unicode
      ordered = [SemanticOrdered [a, b] | a <- take 6 atoms, b <- take 6 atoms]
      sets = [SemanticUnordered (Set.fromList [a, b, SemanticAtom "é"])
             | a <- take 6 atoms, b <- take 6 atoms]
      records = [SemanticRecord (Map.fromList
                  [("é", a), ("a", b), ("\0", SemanticAtom "\0")])
                | a <- take 6 atoms, b <- take 6 atoms]
      deep = [SemanticRecord (Map.fromList
                [("nested", SemanticOrdered
                    [a, SemanticUnordered (Set.fromList [a, b])])
                ,("🙂", SemanticRecord (Map.fromList [("é", b)]))])
             | a <- take 6 ordered, b <- take 6 sets]
      allForms = atoms ++ ordered ++ sets ++ records ++ deep
      exampleApp = GenericApplicationIdentity
        (DeclarationKey "same") (InterfaceRevision "same")
        (Map.fromList
          [ (GenericStaticParameterKey "a", SemanticAtom "same")
          , (GenericStaticParameterKey "🙂",
             SemanticOrdered [SemanticAtom "é",
               SemanticUnordered (Set.fromList [SemanticAtom "\0"])] ) ])

  check "every constructor and arbitrary finite nested sample roundtrips"
    (all (\f -> decodeP8SemanticForm (encodeP8SemanticForm f) == Right f)
      allForms)
  check "recursive independent reference bytes agree with actual codec"
    (all (\f -> encodeFormRef f == encodeP8SemanticForm f) allForms)
  check "full recursive reference compare agrees with derived native Ord"
    (and [compareFormRef x y == compare x y
          | x <- allForms, y <- allForms])
  check "native Text Ord agrees with UTF-8 byte comparison on boundary probes"
    (and [compare x y == compareTextBytes x y
          | x <- unicode, y <- unicode])
  check "constructor order is not lexical wire tag order (u > r)"
    (let u = SemanticUnordered Set.empty
         r = SemanticRecord Map.empty
     in u < r && encodeP8SemanticForm u > encodeP8SemanticForm r)
  check "record insertion order and Set insertion duplicates normalize"
    (let f = SemanticRecord (Map.fromList
                [("b", SemanticAtom "b"), ("a", SemanticAtom "a")])
         g = SemanticRecord (Map.fromList
                [("a", SemanticAtom "a"), ("b", SemanticAtom "b")])
         u = SemanticUnordered (Set.fromList
                [SemanticAtom "é", SemanticAtom "é"])
         v = SemanticUnordered (Set.fromList [SemanticAtom "é"])
     in f == g && encodeP8SemanticForm f == encodeP8SemanticForm g
          && u == v && encodeP8SemanticForm u == encodeP8SemanticForm v)
  check "wire cannot accept duplicate/nonascending recursive keys or members"
    (all (rejected . decodeP8SemanticForm)
      ["r2:t1:aat1:at1:aat1:b"
      ,"r2:t1:bat1:bt1:aat1:a"
      ,"u2:at1:aat1:a"
      ,"u2:at1:bat1:a"
      ,"o2:at1:a"
      ,"o1:u2:at1:aat1:a"])
  check "wire cannot accept malformed nested Unicode or framing"
    (all (rejected . decodeP8SemanticForm)
      [BS.concat ["at3:", BS.pack [237,160,128]]
      ,BS.concat ["r1:t2:", BS.pack [192,128], "at0:"]
      ,"at01:a"
      ,"o0:garbage"
      ,"at1:aextra"])
  check "D/V/Q/M role-tagged generic codec agrees with native"
    (decodeP8GenericApplication (encodeP8GenericApplication exampleApp)
      == Right exampleApp)
  check "Q duplicate and misordered keys, or D/V role substitution reject"
    (all (rejected . decodeP8GenericApplication)
      [ "gDt1:xVt1:y2:Qt1:aMat1:xQt1:aMat1:y"
      , "gDt1:xVt1:y2:Qt1:bMat1:xQt1:aMat1:y"
      , "gVt1:xVt1:y0:"
      , "gDt1:xDt1:y0:" ])
  putStrLn "P8-D2 actual native differential complete"
