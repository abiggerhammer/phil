{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstWholeSource
  ( GrammarV1ReferenceSourceCore
  , grammarV1ProductionSourceCore
  , grammarV1ReferenceSourceCore
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
  input <- TextIO.getContents
  let directCases =
        [ ( "spine-attributes-and-mixed-bodies"
          , Text.unlines
              [ "module demo.main;"
              , "import common.types { Byte, Word };"
              , "@key(\"decl:t\") type T = U8;"
              , "claim Ready = true;"
              , "architecture A { observable metrics.value; }"
              , "program main = instantiate A;"
              ]
          )
        , ( "ordered-declarations"
          , Text.unlines
              [ "type A = U8;"
              , "type B = U16;"
              , "claim First = true;"
              , "claim Second = false;"
              ]
          )
        , ( "unicode-whole-source"
          , Text.unlines
              [ "module δοκιμή.κύριο;"
              , "@key(\"decl:unicode\") type Τύπος = U8;"
              , "architecture Δομή { observable μετρικά.τιμή; }"
              , "program κύριο = instantiate Δομή;"
              ]
          )
        ]
      directResults =
        [ checkSource label source
        | (label, source) <- directCases
        ]
      mismatch = checkMismatch
      caseLines = filter (not . Text.null) (Text.lines input)
      parsedCases = traverse parseCaseLine caseLines
  corpusResults <- case parsedCases of
    Left detail -> pure [Left detail]
    Right cases -> mapM runCase cases
  let failures = [detail | Left detail <- directResults <> [mismatch] <> corpusResults]
  mapM_ (putStrLn . ("FAIL: " <>)) failures
  if null failures
    then putStrLn
      ("PASS: certified Grammar-v1 whole-source AST agrees with production across "
        <> show (length directCases) <> " direct controls and parser corpus")
    else exitFailure

checkSource :: String -> Text -> Either String ()
checkSource label source = do
  (referenceValue, productionValue) <- parseValues (Text.pack label) source
  if referenceValue == productionValue
    then Right ()
    else Left
      (label <> " -- certified/production whole-source mismatch\nreference: "
        <> show referenceValue <> "\nproduction: " <> show productionValue)

checkMismatch :: Either String ()
checkMismatch = do
  (referenceValue, _) <- parseValues
    "mismatch-reference"
    (Text.unlines
      [ "module demo.main;"
      , "@key(\"decl:t\") type T = U8;"
      , "architecture A { constraint true; }"
      , "program main = instantiate A;"
      ])
  (_, productionValue) <- parseValues
    "mismatch-production"
    (Text.unlines
      [ "module demo.main;"
      , "@key(\"decl:t\") type T = U16;"
      , "architecture A { constraint false; }"
      , "program main = instantiate A;"
      ])
  if referenceValue /= productionValue
    then Right ()
    else Left "same-family whole-source body drift was accepted as equal"

parseValues
  :: Text
  -> Text
  -> Either String (GrammarV1ReferenceSourceCore, GrammarV1ReferenceSourceCore)
parseValues sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValue <- mapLeft show (grammarV1ReferenceSourceCore tree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  productionValue <- mapLeft show (grammarV1ProductionSourceCore production)
  pure (referenceValue, productionValue)

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
        Left exception -> Left
          (label <> " -- unable to read fixture: " <> show exception)
        Right source -> checkSource label source

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
