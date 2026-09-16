{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstProviderDeclarations
  ( GrammarV1ReferenceProviderDeclaration
  , grammarV1ProductionProviderDeclarations
  , grammarV1ReferenceProviderDeclarations
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
        [ ("minimal-contract", "provider Store {}", 1)
        , ( "rich-contract"
          , Text.unlines
              [ "provider Store[T: Type] requires { proposition true; } {"
              , "  operation Read : U8;"
              , "  law Safe : true;"
              , "  lifecycle Open : false;"
              , "}"
              ]
          , 1
          )
        , ("minimal-implementation", "provider implementation StoreImpl satisfies Store {}", 1)
        , ( "rich-implementation"
          , Text.unlines
              [ "provider implementation StoreImpl[T: Type] requires { proposition true; } satisfies Store[T] {"
              , "  operation Read satisfies U8 { return 1; }"
              , "  law Safe = true;"
              , "  lifecycle Open = false;"
              , "}"
              ]
          , 1
          )
        , ( "opaque-implementation"
          , "opaque provider implementation Foreign[T: Type] requires { proposition true; } satisfies Store[T];"
          , 1
          )
        , ( "unicode"
          , Text.unlines
              [ "provider Αποθήκη { law Ασφάλεια : true; }"
              , "provider implementation Υλοποίηση satisfies Αποθήκη { lifecycle Ζωή = false; }"
              , "opaque provider implementation Ξένο satisfies Αποθήκη;"
              ]
          , 3
          )
        , ( "mixed-source"
          , Text.unlines
              [ "type T = U8;"
              , "provider P { operation Op : U8; }"
              , "claim C = true;"
              , "provider implementation I satisfies P { operation Op satisfies U8 {} }"
              , "opaque provider implementation O satisfies P;"
              ]
          , 3
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
      ("PASS: certified Grammar-v1 provider declarations agree with production AST across "
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
          <> " provider declarations, got " <> show (length referenceValues))
      else Right ()

checkMismatch :: Either String ()
checkMismatch = do
  (referenceValues, _) <- parseValues
    "mismatch-reference"
    "provider P { operation Op : U8; }"
  (_, productionValues) <- parseValues
    "mismatch-production"
    "provider P { operation Op : U16; }"
  if referenceValues /= productionValues
    then Right ()
    else Left "mismatched provider operation types were accepted as equal"

parseValues
  :: Text
  -> Text
  -> Either String
      ( [GrammarV1ReferenceProviderDeclaration]
      , [GrammarV1ReferenceProviderDeclaration]
      )
parseValues sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show (grammarV1ReferenceProviderDeclarations tree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  pure (referenceValues, grammarV1ProductionProviderDeclarations production)

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
