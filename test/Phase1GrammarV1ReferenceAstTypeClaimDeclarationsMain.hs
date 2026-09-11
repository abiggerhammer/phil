{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstTypeClaimDeclarations
  ( GrammarV1ReferenceTypeClaimDeclaration
  , grammarV1ProductionTypeClaimDeclarations
  , grammarV1ReferenceTypeClaimDeclarations
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
        [ ("minimal-type", "type T = U8;", 1)
        , ("rich-type", "type Box[A: Type] requires { proposition true; } = (A, Bytes[4]);", 1)
        , ("minimal-claim", "claim Marker;", 1)
        , ("empty-claim-params", "claim Empty() = true;", 1)
        , ("rich-claim", "claim Equal[T: Type] requires { proposition true; } (x: T, y: T) = x == y;", 1)
        , ("unicode-claim", "claim Μέτρηση(x: U32) = x == 1;", 1)
        , ("mixed-source", "record R {x: U8}\ntype T = U16;\ndata D = A;\nclaim P = true;", 2)
        ]
      directResults =
        [checkSource label source expected | (label, source, expected) <- directCases]
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
      ("PASS: certified Grammar-v1 type/claim declarations agree with production AST across "
        <> show (length directCases) <> " direct controls and parser corpus")
    else exitFailure

checkSource :: String -> Text -> Int -> Either String ()
checkSource label source expectedCount = do
  (referenceValues, productionValues) <- parseValues (Text.pack label) source
  if referenceValues /= productionValues
    then Left
      (label <> " -- certified/production mismatch\nreference: "
        <> show referenceValues <> "\nproduction: " <> show productionValues)
    else if length referenceValues /= expectedCount
      then Left
        (label <> " -- expected " <> show expectedCount
          <> " type/claim declarations, got " <> show (length referenceValues))
      else Right ()

checkMismatch :: Either String ()
checkMismatch = do
  (referenceValues, _) <- parseValues "mismatch-reference" "type T = U8;"
  (_, productionValues) <- parseValues "mismatch-production" "type T = U16;"
  if referenceValues /= productionValues
    then Right ()
    else Left "mismatched type-alias payloads were accepted as equal"

parseValues
  :: Text
  -> Text
  -> Either String
      ( [GrammarV1ReferenceTypeClaimDeclaration]
      , [GrammarV1ReferenceTypeClaimDeclaration]
      )
parseValues sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show (grammarV1ReferenceTypeClaimDeclarations tree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  pure (referenceValues, grammarV1ProductionTypeClaimDeclarations production)

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
          sourceName = Text.pack relativePath
      sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text)
      pure $ case sourceResult of
        Left exception -> Left
          (label <> " -- unable to read fixture: " <> show exception)
        Right source -> do
          (referenceValues, productionValues) <- parseValues sourceName source
          if referenceValues == productionValues
            then Right ()
            else Left
              (label <> " -- certified/production mismatch\nreference: "
                <> show referenceValues <> "\nproduction: " <> show productionValues)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
