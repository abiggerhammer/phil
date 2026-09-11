{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstCapabilityBoundary
  ( GrammarV1ReferenceCapabilityBoundaryDeclaration
  , grammarV1ProductionCapabilityBoundaryDeclarations
  , grammarV1ReferenceCapabilityBoundaryDeclarations
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
        [ ("minimal-capability", "capability Access mode unrestricted {}", 1)
        , ( "rich-capability"
          , Text.unlines
              [ "capability Access[T: Type] mode affine requires { proposition true; } {"
              , "  permits Audit[U8];"
              , "  requires false;"
              , "  law Safe : true;"
              , "}"
              ]
          , 1
          )
        , ("minimal-boundary", "boundary Wire : U8 {}", 1)
        , ( "rich-boundary"
          , Text.unlines
              [ "boundary Wire[T: Type] requires { proposition true; } : Frame[Transport] {"
              , "  receive using Inbound[U8];"
              , "  send using Outbound[U16];"
              , "  correspondence true;"
              , "  canonical;"
              , "  failure Bytes[4];"
              , "  law RoundTrip : false;"
              , "}"
              ]
          , 1
          )
        , ( "unicode"
          , Text.unlines
              [ "capability Δύναμη mode linear { law Νόμος : true; }"
              , "boundary Σύνορο : U32 { canonical; }"
              ]
          , 2
          )
        , ( "mixed-source"
          , Text.unlines
              [ "type T = U8;"
              , "capability C mode unrestricted { permits Audit; }"
              , "claim P = true;"
              , "boundary B : U16 { failure U8; }"
              ]
          , 2
          )
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
      ("PASS: certified Grammar-v1 capability/boundary declarations agree with production AST across "
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
          <> " capability/boundary declarations, got " <> show (length referenceValues))
      else Right ()

checkMismatch :: Either String ()
checkMismatch = do
  (referenceValues, _) <- parseValues
    "mismatch-reference"
    "boundary B : U8 { failure U16; }"
  (_, productionValues) <- parseValues
    "mismatch-production"
    "boundary B : U8 { failure U32; }"
  if referenceValues /= productionValues
    then Right ()
    else Left "mismatched boundary failure payloads were accepted as equal"

parseValues
  :: Text
  -> Text
  -> Either String
      ( [GrammarV1ReferenceCapabilityBoundaryDeclaration]
      , [GrammarV1ReferenceCapabilityBoundaryDeclaration]
      )
parseValues sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show
    (grammarV1ReferenceCapabilityBoundaryDeclarations tree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  pure
    ( referenceValues
    , grammarV1ProductionCapabilityBoundaryDeclarations production
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
