{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer
  ( GrammarV1Token
  , lexGrammarV1SourceTokens
  , runtimeBytesLengthMarker
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  , grammarV1ReferenceParseSourceTokens
  , grammarV1ReferenceParseTreeTokens
  , kernelStringToText
  , textToKernelString
  )
import Phil.Surface.GrammarV1.ReferenceToken
  ( GrammarV1ReferenceToken (..)
  , grammarV1ReferenceToken
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

corpusRoot :: FilePath
corpusRoot = "test/fixtures/phase1-surface"

data CorpusCase = CorpusCase
  { corpusCaseId :: Text
  , corpusCasePath :: FilePath
  , corpusCaseExpectation :: Text
  }

main :: IO ()
main = do
  let directChecks =
        [ utf8RoundTrip
        , sourceTreeRoundTrip "unicode identifier" "type Café = U32;"
        , bareBytesTreeRoundTrip
        ]
      directFailures = [detail | Left detail <- directChecks]
  mapM_ (putStrLn . ("FAIL: " <>)) directFailures
  if null directFailures then pure () else exitFailure

  input <- TextIO.getContents
  case traverse parseCaseLine (filter (not . Text.null) (Text.lines input)) of
    Left detail -> putStrLn ("FAIL: manifest stream -- " <> detail) >> exitFailure
    Right [] -> putStrLn "FAIL: manifest stream -- no corpus cases" >> exitFailure
    Right cases -> do
      results <- traverse runCase cases
      let failures = [detail | Left detail <- results]
      mapM_ (putStrLn . ("FAIL: " <>)) failures
      if null failures
        then putStrLn
          ("PASS: certified Grammar-v1 parse-tree bridge preserves structure and leaves ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

utf8RoundTrip :: Either String ()
utf8RoundTrip =
  case kernelStringToText (textToKernelString "Aéλ") of
    Right decoded
      | decoded == "Aéλ" -> Right ()
      | otherwise -> Left ("UTF-8 round trip changed text to " <> show decoded)
    Left failure -> Left ("UTF-8 round trip failed: " <> show failure)

sourceTreeRoundTrip :: String -> Text -> Either String ()
sourceTreeRoundTrip label source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  checkReferenceTree label sourceTokens tree

bareBytesTreeRoundTrip :: Either String ()
bareBytesTreeRoundTrip = do
  let source = "type Blob = Bytes;"
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens "bare-bytes-tree" source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  checkReferenceTree "bare Bytes" sourceTokens tree
  let leaves = grammarV1ReferenceParseTreeTokens tree
  if any (referenceTokenContains runtimeBytesLengthMarker) leaves
    then Left "bare Bytes certified tree contains production-only synthetic length marker"
    else Right ()

referenceTokenContains :: Text -> GrammarV1ReferenceToken -> Bool
referenceTokenContains needle token = case token of
  GrammarV1LiteralToken value -> value == needle
  GrammarV1LexicalToken className lexeme ->
    className == needle || lexeme == needle

checkReferenceTree
  :: String
  -> [Located GrammarV1Token]
  -> GrammarV1ReferenceParseTree
  -> Either String ()
checkReferenceTree label sourceTokens tree = do
  case tree of
    GrammarV1ReferenceNonterminal "source_file" _ -> Right ()
    GrammarV1ReferenceNonterminal other _ ->
      Left (label <> " -- expected source_file root, got " <> show other)
    other -> Left (label <> " -- expected nonterminal root, got " <> show other)
  let expectedLeaves = map (grammarV1ReferenceToken . locatedValue) sourceTokens
      actualLeaves = grammarV1ReferenceParseTreeTokens tree
  if actualLeaves == expectedLeaves
    then Right ()
    else Left
      (label <> " -- certified tree leaves differ from canonical source tokens\nexpected: "
        <> show expectedLeaves <> "\nactual:   " <> show actualLeaves)

parseCaseLine :: Text -> Either String CorpusCase
parseCaseLine line = case Text.splitOn "\t" line of
  [fixtureId, path, expectation]
    | not (Text.null fixtureId)
    , not (Text.null path)
    , expectation == "parse" || expectation == "reject-syntax" ->
        Right CorpusCase
          { corpusCaseId = fixtureId
          , corpusCasePath = Text.unpack path
          , corpusCaseExpectation = expectation
          }
  _ -> Left ("invalid TSV row " <> show line)

runCase :: CorpusCase -> IO (Either String ())
runCase corpusCase = do
  let relativePath = corpusCasePath corpusCase
      path = corpusRoot <> "/" <> relativePath
      label = Text.unpack (corpusCaseId corpusCase) <> " " <> relativePath
      sourceName = Text.pack relativePath
  sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text)
  pure $ case sourceResult of
    Left exception -> Left (label <> " -- unable to read fixture: " <> show exception)
    Right source -> case lexGrammarV1SourceTokens sourceName source of
      Left diagnostic
        | corpusCaseExpectation corpusCase == "reject-syntax" -> Right ()
        | otherwise -> Left (label <> " -- lexical rejection: " <> show diagnostic)
      Right sourceTokens -> case grammarV1ReferenceParseSourceTokens sourceTokens of
        Left failure
          | corpusCaseExpectation corpusCase == "reject-syntax" -> Right ()
          | otherwise -> Left (label <> " -- certified parse failed: " <> show failure)
        Right tree
          | corpusCaseExpectation corpusCase == "reject-syntax" ->
              Left (label <> " -- syntax-negative fixture produced certified tree")
          | otherwise -> checkReferenceTree label sourceTokens tree

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
