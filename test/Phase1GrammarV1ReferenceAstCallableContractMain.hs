{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstCallableContract
  ( GrammarV1ReferenceCallableContractDeclaration
  , grammarV1ProductionCallableContractDeclarations
  , grammarV1ReferenceCallableContractDeclarations
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
        [ ("minimal", "callable C() -> Unit {}", 1)
        , ("all-clauses", fullCallableSource, 1)
        , ("rich-residue", richResidueSource, 1)
        , ("empty-sets", emptySetsSource, 1)
        , ("unicode", "callable Μέτρηση(τιμή: U32) -> U32 { requires true; }", 1)
        , ("mixed-source", "type T = U8;\ncallable C() -> Unit {}\nclaim P = true;", 1)
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
      ("PASS: certified Grammar-v1 callable contracts agree with production AST across "
        <> show (length directCases) <> " direct controls and parser corpus")
    else exitFailure

fullCallableSource :: Text
fullCallableSource = Text.unlines
  [ "callable C[E : Effects] requires { effects E within {IO, Audit}; } (x : U32) -> Unit {"
  , "  requires true;"
  , "  consumes {x, store.slot};"
  , "  borrows {loan};"
  , "  authority {Cap, OtherCap};"
  , "  effects {IO, Audit(x)};"
  , "  outcomes {success Unit};"
  , "  outcome success Unit {}"
  , "  ensures true;"
  , "  obligation true;"
  , "  assumes true;"
  , "  cost 7;"
  , "  callee preserve;"
  , "}"
  ]

richResidueSource :: Text
richResidueSource = Text.unlines
  [ "callable Flow[T : Type]() -> Unit {"
  , "  outcomes {success Unit, negative U8, terminal Unit, fatal Unit};"
  , "  outcome negative U8 {"
  , "    state (code: U8, payload: Bytes[4]);"
  , "    callee replace with Next[U8] state 1;"
  , "    ensures true;"
  , "    obligation false;"
  , "  }"
  , "  callee consume;"
  , "}"
  ]

emptySetsSource :: Text
emptySetsSource = Text.unlines
  [ "callable Empty() -> Unit {"
  , "  consumes {};"
  , "  borrows {};"
  , "  authority {};"
  , "  effects {};"
  , "  outcomes {};"
  , "  outcome terminal Unit { state (); }"
  , "}"
  ]

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
          <> " callable declarations, got " <> show (length referenceValues))
      else Right ()

checkMismatch :: Either String ()
checkMismatch = do
  (referenceValues, _) <- parseValues
    "mismatch-reference"
    "callable C() -> Unit { callee replace with Next state 1; }"
  (_, productionValues) <- parseValues
    "mismatch-production"
    "callable C() -> Unit { callee replace with Next state 2; }"
  if referenceValues /= productionValues
    then Right ()
    else Left "mismatched callable callee-state payloads were accepted as equal"

parseValues
  :: Text
  -> Text
  -> Either String
      ( [GrammarV1ReferenceCallableContractDeclaration]
      , [GrammarV1ReferenceCallableContractDeclaration]
      )
parseValues sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show (grammarV1ReferenceCallableContractDeclarations tree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  pure (referenceValues, grammarV1ProductionCallableContractDeclarations production)

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
