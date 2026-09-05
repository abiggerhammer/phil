{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Either (isLeft, isRight)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarRevisionCertification
import Phil.Surface.Lineage
import System.Exit (exitFailure)

main :: IO ()
main = do
  inlineFixture <- TextIO.readFile "test/fixtures/phase1/surf010-inline.bundle"
  metadataFixture <- TextIO.readFile "test/fixtures/phase1/surf010-metadata.bundle"
  results <- sequence
    [ test "production grammar revision certifies inline SourceBundle"
        (certifies canonicalGrammarRevisionV1 inlineFixture)
    , test "production grammar revision certifies metadata SourceBundle"
        (certifies canonicalGrammarRevisionV1 metadataFixture)
    , test "payload/carrier variation cannot rebind selected grammar revision"
        (sameBoundRevision inlineFixture metadataFixture)
    , test "native missing-revision diagnostic precedes kernel admission"
        (expectNative isMissing missingRevisionBundle)
    , test "native malformed-revision diagnostic precedes kernel admission"
        (expectNative isMalformed malformedRevisionBundle)
    , test "native incompatible-revision diagnostic precedes kernel admission"
        (expectNative isIncompatible incompatibleRevisionBundle)
    , test "exact grammar revision kernel facts are accepted"
        (expectKernel isRight (GrammarRevisionKernelFacts True True True))
    , test "kernel rejects absent/incompetent revision fact"
        (expectKernel isLeft (GrammarRevisionKernelFacts False True True))
    , test "kernel rejects selected-revision mismatch fact"
        (expectKernel isLeft (GrammarRevisionKernelFacts True False True))
    , test "kernel rejects payload-rebinding disagreement fact"
        (expectKernel isLeft (GrammarRevisionKernelFacts True True False))
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

certifies :: GrammarRevision -> Text -> Either String ()
certifies expected source = case certifyPortableSourceBundleGrammar expected source of
  Left errorValue -> Left ("certification rejected: " <> show errorValue)
  Right certified -> assert
    (portableGrammarRevision (certifiedGrammarRevisionBundle certified) == expected)
    "certified bundle did not retain selected grammar revision"

sameBoundRevision :: Text -> Text -> Either String ()
sameBoundRevision firstSource secondSource = do
  first <- mapLeft showCertification
    (certifyPortableSourceBundleGrammar canonicalGrammarRevisionV1 firstSource)
  second <- mapLeft showCertification
    (certifyPortableSourceBundleGrammar canonicalGrammarRevisionV1 secondSource)
  let firstRevision = portableGrammarRevision (certifiedGrammarRevisionBundle first)
      secondRevision = portableGrammarRevision (certifiedGrammarRevisionBundle second)
  assert
    (firstRevision == canonicalGrammarRevisionV1
      && secondRevision == canonicalGrammarRevisionV1)
    "payload/carrier variation changed selected grammar revision"

expectNative :: (LineageError -> Bool) -> Text -> Either String ()
expectNative predicate source =
  case certifyPortableSourceBundleGrammar canonicalGrammarRevisionV1 source of
    Left (GrammarRevisionNativeError errorValue)
      | predicate errorValue -> Right ()
      | otherwise -> Left ("unexpected native diagnostic: " <> show errorValue)
    Left other -> Left ("kernel disagreement preceded native diagnostic: " <> show other)
    Right certified -> Left ("expected native rejection, got: " <> show certified)

expectKernel
  :: (Either GrammarRevisionCertificationError () -> Bool)
  -> GrammarRevisionKernelFacts
  -> Either String ()
expectKernel predicate facts =
  let result = verifyGrammarRevisionKernelFacts facts
  in assert (predicate result) ("unexpected kernel result: " <> show result)

missingRevisionBundle :: Text
missingRevisionBundle = Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "root\tprogram:test"
  ]

malformedRevisionBundle :: Text
malformedRevisionBundle = Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "grammar\tsha256:ABC"
  , "root\tprogram:test"
  ]

incompatibleRevisionBundle :: Text
incompatibleRevisionBundle = Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "grammar\tsha256:" <> Text.replicate 64 "0"
  , "root\tprogram:test"
  ]

isMissing :: LineageError -> Bool
isMissing MissingGrammarRevision = True
isMissing _ = False

isMalformed :: LineageError -> Bool
isMalformed MalformedGrammarRevision {} = True
isMalformed _ = False

isIncompatible :: LineageError -> Bool
isIncompatible IncompatibleGrammarRevision {} = True
isIncompatible _ = False

showCertification :: GrammarRevisionCertificationError -> String
showCertification = show

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
