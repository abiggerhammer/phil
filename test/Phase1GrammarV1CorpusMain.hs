{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Parser
import System.Exit (exitFailure)

corpusRoot :: FilePath
corpusRoot = "test/fixtures/phase1-surface"

data CorpusCase = CorpusCase
  { corpusCaseId :: Text.Text
  , corpusCasePath :: FilePath
  , corpusCaseExpectation :: Text.Text
  }

main :: IO ()
main = do
  input <- TextIO.getContents
  case traverse parseCaseLine (filter (not . Text.null) (Text.lines input)) of
    Left detail -> putStrLn ("FAIL: manifest stream -- " <> detail) >> exitFailure
    Right [] -> putStrLn "FAIL: manifest stream -- no corpus cases" >> exitFailure
    Right cases -> do
      results <- traverse runCase cases
      let failures = [detail | Left detail <- results]
      mapM_ putStrLn ["FAIL: " <> detail | detail <- failures]
      if null failures
        then putStrLn ("PASS: manifest-driven Grammar-v1 corpus (" <> show (length cases) <> " fixtures)")
        else exitFailure

parseCaseLine :: Text.Text -> Either String CorpusCase
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
  sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text.Text)
  pure $ case sourceResult of
    Left exception -> Left (label <> " -- unable to read fixture: " <> show exception)
    Right source ->
      let parsed = parseGrammarV1StructuralSource (Text.pack relativePath) source
      in case corpusCaseExpectation corpusCase of
          "parse" -> case parsed of
            Right _ -> Right ()
            Left diagnostic -> Left (label <> " -- expected parse, got " <> show diagnostic)
          "reject-syntax" -> case parsed of
            Left _ -> Right ()
            Right value -> Left (label <> " -- expected syntax rejection, parsed " <> show value)
          other -> Left (label <> " -- unsupported expectation " <> Text.unpack other)
