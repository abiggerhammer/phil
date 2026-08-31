{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as ByteString
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Data.Word (Word8)
import Numeric (showHex)
import Phil.Surface.Lineage
import System.Exit (exitFailure)

main :: IO ()
main = do
  fixture <- TextIO.readFile "test/fixtures/phase1/surf010-inline.bundle"
  results <- sequence
    [ testIO "SURF-006 canonical revision is the exact Grammar-v1 SHA-256" canonicalRevisionMatchesGrammar
    , test "SURF-006 exact grammar revision is admitted" (exactRevisionAccepted fixture)
    , test "SURF-006 missing grammar revision fails closed" missingRevisionRejects
    , test "SURF-006 duplicate grammar revision fails closed" duplicateRevisionRejects
    , test "SURF-006 malformed grammar revision fails closed" malformedRevisionRejects
    , test "SURF-006 incompatible exact grammar revision fails closed" incompatibleRevisionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

canonicalRevisionMatchesGrammar :: IO (Either String ())
canonicalRevisionMatchesGrammar = do
  grammarBytes <- ByteString.readFile "grammar/phase1-surface.ebnf"
  pure $ assert
    (revisionForBytes grammarBytes == canonicalGrammarRevisionV1)
    "canonicalGrammarRevisionV1 does not match grammar/phase1-surface.ebnf"

exactRevisionAccepted :: Text -> Either String ()
exactRevisionAccepted source = case decodePortableSourceBundle source of
  Left errorValue -> Left ("exact revision rejected: " <> show errorValue)
  Right bundle -> assert
    (portableGrammarRevision bundle == canonicalGrammarRevisionV1)
    "decoded bundle did not retain the canonical grammar revision"

missingRevisionRejects :: Either String ()
missingRevisionRejects = expectError isMissing $ Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "root\tprogram:test"
  , "unit\tunit.test\tsite.test\tdecl:test\trecord Test {}"
  ]
  where
    isMissing MissingGrammarRevision = True
    isMissing _ = False

duplicateRevisionRejects :: Either String ()
duplicateRevisionRejects = expectError isDuplicate $ Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , grammarRecord canonicalGrammarRevisionV1
  , grammarRecord canonicalGrammarRevisionV1
  , "root\tprogram:test"
  , "unit\tunit.test\tsite.test\tdecl:test\trecord Test {}"
  ]
  where
    isDuplicate DuplicateGrammarRevision {} = True
    isDuplicate _ = False

malformedRevisionRejects :: Either String ()
malformedRevisionRejects = expectError isMalformed $ Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "grammar\tsha256:ABC"
  , "root\tprogram:test"
  , "unit\tunit.test\tsite.test\tdecl:test\trecord Test {}"
  ]
  where
    isMalformed MalformedGrammarRevision {} = True
    isMalformed _ = False

incompatibleRevisionRejects :: Either String ()
incompatibleRevisionRejects = expectError isMismatch $ Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , grammarRecord incompatible
  , "root\tprogram:test"
  , "unit\tunit.test\tsite.test\tdecl:test\trecord Test {}"
  ]
  where
    incompatible = GrammarRevision ("sha256:" <> Text.replicate 64 "0")
    isMismatch (IncompatibleGrammarRevision expected actual) =
      expected == canonicalGrammarRevisionV1 && actual == incompatible
    isMismatch _ = False

expectError :: (LineageError -> Bool) -> Text -> Either String ()
expectError predicate source = case decodePortableSourceBundle source of
  Left errorValue
    | predicate errorValue -> Right ()
    | otherwise -> Left ("unexpected revision error: " <> show errorValue)
  Right bundle -> Left ("expected revision rejection, decoded: " <> show bundle)

grammarRecord :: GrammarRevision -> Text
grammarRecord revisionValue = "grammar\t" <> unGrammarRevision revisionValue

revisionForBytes :: ByteString.ByteString -> GrammarRevision
revisionForBytes bytes = GrammarRevision
  ("sha256:" <> Text.pack (concatMap hexByte (ByteString.unpack (SHA256.hash bytes))))

hexByte :: Word8 -> String
hexByte value = case showHex value "" of
  [digit] -> ['0', digit]
  digits -> digits

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
