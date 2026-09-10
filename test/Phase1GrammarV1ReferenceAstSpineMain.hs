{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstSpine
  ( grammarV1ProductionSourceSpine
  , grammarV1ReferenceSourceSpine
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( grammarV1ReferenceParseSourceTokens
  )
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
  let directSources =
        [ ("module/import spine",
            "module alpha.beta; import foo.bar; import baz { one, two }; type X = U32;")
        , ("empty prelude spine", "type Blob = Bytes;")
        ]
      directFailures =
        [ detail
        | (label, source) <- directSources
        , Left detail <- [checkSource label source]
        ]
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
          ("PASS: certified Grammar-v1 source-file AST spine agrees with production ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

checkSource :: String -> Text -> Either String ()
checkSource label source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens (Text.pack label) source)
  referenceTree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceSpine <- mapLeft show (grammarV1ReferenceSourceSpine referenceTree)
  productionAst <- mapLeft show (parseGrammarV1StructuralSource (Text.pack label) source)
  let productionSpine = grammarV1ProductionSourceSpine productionAst
  if referenceSpine == productionSpine
    then Right ()
    else Left
      (label <> " -- source-file spine mismatch\nreference: "
        <> show referenceSpine <> "\nproduction: " <> show productionSpine)

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
runCase corpusCase
  | corpusCaseExpectation corpusCase == "reject-syntax" = pure (Right ())
  | otherwise = do
      let relativePath = corpusCasePath corpusCase
          path = corpusRoot <> "/" <> relativePath
          label = Text.unpack (corpusCaseId corpusCase) <> " " <> relativePath
      sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text)
      pure $ case sourceResult of
        Left exception -> Left (label <> " -- unable to read fixture: " <> show exception)
        Right source -> checkSource label source

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
