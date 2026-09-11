{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstProtocolDeclaration
  ( GrammarV1ReferenceProtocolDeclarationCore
  , grammarV1ProductionProtocolDeclarations
  , grammarV1ReferenceProtocolDeclarations
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
        [ ( "minimal"
          , "protocol P { role A = end Done; role B = end Done; }"
          , 1
          )
        , ( "rich"
          , Text.unlines
              [ "protocol Wire[T: Type] requires { proposition true; } {"
              , "  role Client = send (x: T) using Codec when true then select {"
              , "    Ok() => end Done | Retry(y: U8) => end RetryDone"
              , "  };"
              , "  role Server = recursive Loop = receive (x: T) using Codec when true then offer {"
              , "    Ok => end Done | Retry() => continue Loop"
              , "  };"
              , "}"
              ]
          , 1
          )
        , ( "static-session-reference"
          , "protocol Ref { role Left = Sess[U8]; role Right = Sess[U16]; }"
          , 1
          )
        , ( "unicode"
          , "protocol Πρωτόκολλο { role Πελάτης = end Τέλος; role Διακομιστής = end Τέλος; }"
          , 1
          )
        , ( "mixed"
          , Text.unlines
              [ "type T = U8;"
              , "protocol First { role A = end X; role B = end Y; }"
              , "claim C = true;"
              , "protocol Second { role C = end Z; role D = end W; }"
              ]
          , 2
          )
        ]
      directResults =
        [ checkSource label source expected
        | (label, source, expected) <- directCases
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
      ("PASS: certified Grammar-v1 protocol declarations agree with production AST across "
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
          <> " protocol declarations, got " <> show (length referenceValues))
      else Right ()

checkMismatch :: Either String ()
checkMismatch = do
  (referenceValues, _) <- parseValues
    "mismatch-reference"
    "protocol P { role A = send (x: U8) then end Done; role B = end Done; }"
  (_, productionValues) <- parseValues
    "mismatch-production"
    "protocol P { role A = send (x: U16) then end Done; role B = end Done; }"
  if referenceValues /= productionValues
    then Right ()
    else Left "mismatched protocol role-session payloads were accepted as equal"

parseValues
  :: Text
  -> Text
  -> Either String
      ( [GrammarV1ReferenceProtocolDeclarationCore]
      , [GrammarV1ReferenceProtocolDeclarationCore]
      )
parseValues sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show (grammarV1ReferenceProtocolDeclarations tree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  pure
    ( referenceValues
    , grammarV1ProductionProtocolDeclarations production
    )

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
