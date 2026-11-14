{-# LANGUAGE OverloadedStrings #-}

-- P8 proof-lane data-level codec only. Not accepted native↔Rocq authority.
module Phil.Verification.P8SemanticFormCodec
  ( encodeP8SemanticForm, decodeP8SemanticForm
  , encodeP8GenericApplication, decodeP8GenericApplication
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BB
import qualified Data.ByteString.Lazy as Lazy
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.Encoding as TE
import Data.Word (Word8)
import Phil.Core.Generic
  ( GenericApplicationIdentity (..), GenericStaticParameterKey (..) )
import Phil.Core.Static
  ( DeclarationKey (..), InterfaceRevision (..), SemanticForm (..) )

-- A diagnostic wire grammar, not a new Phil source representation.
-- text = t + canonical-decimal UTF-8 byte length + : + exact UTF-8 bytes
-- form = a text | o count : form* | u count : sorted-form*
--      | r count : (sorted-text-key form)*
-- app  = g D text V text count : (Q text M form)*
-- Each count is canonical decimal; Q keys, record fields and set members
-- MUST be strictly ascending according to actual native Haskell Ord.
-- No fixed-width length narrows the original accepted in-memory domain.
type Parser a = BS.ByteString -> Either String (a, BS.ByteString)

encodeP8SemanticForm :: SemanticForm -> BS.ByteString
encodeP8SemanticForm = render . putForm

decodeP8SemanticForm :: BS.ByteString -> Either String SemanticForm
decodeP8SemanticForm = exact parseForm

encodeP8GenericApplication :: GenericApplicationIdentity -> BS.ByteString
encodeP8GenericApplication = render . putApplication

decodeP8GenericApplication
  :: BS.ByteString -> Either String GenericApplicationIdentity
decodeP8GenericApplication = exact parseApplication

render :: BB.Builder -> BS.ByteString
render = Lazy.toStrict . BB.toLazyByteString

tag :: Word8 -> BB.Builder
tag = BB.word8

count :: Int -> BB.Builder
count n = BB.intDec n <> tag 58

putText :: Text -> BB.Builder
putText txt = let bytes = TE.encodeUtf8 txt
              in tag 116 <> count (BS.length bytes) <> BB.byteString bytes

putForm :: SemanticForm -> BB.Builder
putForm form = case form of
  SemanticAtom txt -> tag 97 <> putText txt
  SemanticOrdered xs -> tag 111 <> count (length xs) <> foldMap putForm xs
  SemanticUnordered xs ->
    tag 117 <> count (Set.size xs) <> foldMap putForm (Set.toAscList xs)
  SemanticRecord fields ->
    tag 114 <> count (Map.size fields)
      <> foldMap (\(k,v) -> putText k <> putForm v) (Map.toAscList fields)

putApplication :: GenericApplicationIdentity -> BB.Builder
putApplication app =
  tag 103
  <> tag 68 <> putText (unDeclarationKey (genericApplicationDeclarationKey app))
  <> tag 86 <> putText (unInterfaceRevision (genericApplicationInterfaceRevision app))
  <> count (Map.size actuals)
  <> foldMap (\(k,v) ->
      tag 81 <> putText (unGenericStaticParameterKey k)
      <> tag 77 <> putForm v) (Map.toAscList actuals)
 where
  actuals = genericApplicationSemanticArguments app

exact :: Parser a -> BS.ByteString -> Either String a
exact parser input = do
  (value, trailing) <- parser input
  if BS.null trailing then Right value else Left "trailing bytes"

expect :: Word8 -> BS.ByteString -> Either String BS.ByteString
expect wanted input = case BS.uncons input of
  Just (actual, remainder) | actual == wanted -> Right remainder
  _ -> Left "wrong or missing tag"

readCount :: Parser Integer
readCount input =
  let (digits, rest) = BS.break (== 58) input
      valid = not (BS.null digits)
        && (BS.length digits == 1 || BS.head digits /= 48)
        && BS.all (\b -> b >= 48 && b <= 57) digits
  in case BS.uncons rest of
      Just (_, remainder) | valid ->
        Right (BS.foldl' (\n b -> n * 10 + toInteger b - 48) 0 digits,
               remainder)
      _ -> Left "invalid canonical decimal count"

parseText :: Parser Text
parseText input = do
  afterTag <- expect 116 input
  (n, remaining) <- readCount afterTag
  if n > toInteger (BS.length remaining)
    then Left "text byte length exceeds available input"
    else let (wire, trailing) = BS.splitAt (fromInteger n) remaining
         in case TE.decodeUtf8' wire of
              Left _ -> Left "invalid UTF-8 text"
              Right txt -> Right (txt, trailing)

parseMany :: Integer -> Parser a -> Parser [a]
parseMany n parser input
  | n > toInteger (BS.length input) = Left "count exceeds available input"
  | otherwise = go n input []
 where
  go 0 rest accumulated = Right (reverse accumulated, rest)
  go remaining rest accumulated = do
    (one, after) <- parser rest
    go (remaining - 1) after (one : accumulated)

strictAsc :: Ord a => [a] -> Bool
strictAsc xs = and (zipWith (<) xs (drop 1 xs))

parseForm :: Parser SemanticForm
parseForm input = case BS.uncons input of
  Nothing -> Left "missing form tag"
  Just (formTag, rest) -> case formTag of
    97 -> do
      (txt, after) <- parseText rest
      Right (SemanticAtom txt, after)
    111 -> do
      (n, afterCount) <- readCount rest
      (xs, after) <- parseMany n parseForm afterCount
      Right (SemanticOrdered xs, after)
    117 -> do
      (n, afterCount) <- readCount rest
      (xs, after) <- parseMany n parseForm afterCount
      if strictAsc xs
        then Right (SemanticUnordered (Set.fromDistinctAscList xs), after)
        else Left "unordered set is duplicate or unsorted by native Ord"
    114 -> do
      (n, afterCount) <- readCount rest
      (fields, after) <- parseMany n parseField afterCount
      if strictAsc (map fst fields)
        then Right (SemanticRecord (Map.fromDistinctAscList fields), after)
        else Left "record keys are duplicate or unsorted by native Ord"
    _ -> Left "unknown form constructor tag"

parseField :: Parser (Text, SemanticForm)
parseField input = do
  (key, afterKey) <- parseText input
  (value, afterValue) <- parseForm afterKey
  Right ((key, value), afterValue)

parseRoleText :: Word8 -> Parser Text
parseRoleText role input = expect role input >>= parseText

parseArgument :: Parser (GenericStaticParameterKey, SemanticForm)
parseArgument input = do
  (key, afterKey) <- parseRoleText 81 input
  afterValueRole <- expect 77 afterKey
  (value, after) <- parseForm afterValueRole
  Right ((GenericStaticParameterKey key, value), after)

parseApplication :: Parser GenericApplicationIdentity
parseApplication input = do
  afterTag <- expect 103 input
  (declaration, afterDeclaration) <- parseRoleText 68 afterTag
  (revision, afterRevision) <- parseRoleText 86 afterDeclaration
  (n, afterCount) <- readCount afterRevision
  (actuals, after) <- parseMany n parseArgument afterCount
  if strictAsc (map fst actuals)
    then Right
      (GenericApplicationIdentity
        (DeclarationKey declaration)
        (InterfaceRevision revision)
        (Map.fromDistinctAscList actuals), after)
    else Left "duplicate or unsorted generic Q keys"
