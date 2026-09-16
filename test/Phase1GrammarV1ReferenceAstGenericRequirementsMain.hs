{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstGenericRequirements
  ( GrammarV1ReferenceEffectSetTag (..)
  , GrammarV1ReferenceGenericRequirementSpine (..)
  , grammarV1ProductionTypeAliasRequirementSpines
  , grammarV1ReferenceTypeAliasRequirementSpines
  )
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeTag (..)
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
  let directChecks =
        [ checkNoRequirements
        , checkAllRequirementAlternatives
        , checkEffectReference
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
          ("PASS: certified Grammar-v1 generic requirements agree with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

checkNoRequirements :: Either String ()
checkNoRequirements = do
  (referenceValues, productionValues) <-
    parseRequirementSpines "no-requirements" "type Plain = Unit;"
  if referenceValues == [[]] && productionValues == referenceValues
    then Right ()
    else Left
      ("no requirements -- unexpected projection\nreference: "
        <> show referenceValues <> "\nproduction: " <> show productionValues)

checkAllRequirementAlternatives :: Either String ()
checkAllRequirementAlternatives = do
  let source = Text.unlines
        [ "type Requirements[T : Type] requires {"
        , "  structural T : Dup;"
        , "  proposition true;"
        , "  provider P : Unit;"
        , "  callable C : Bool;"
        , "  boundary B : U8;"
        , "  architecture A : I16;"
        , "  effects E within {};"
        , "  authority F32;"
        , "  boundary representation String;"
        , "  representation true;"
        , "  placement false;"
        , "  cost true;"
        , "  environment false;"
        , "} = Unit;"
        ]
      expected =
        [ GrammarV1ReferenceStructuralRequirement "T" "Dup"
        , GrammarV1ReferencePropositionRequirement
        , GrammarV1ReferenceProviderRequirement
            "P" GrammarV1ReferenceUnitType
        , GrammarV1ReferenceCallableRequirement
            "C" GrammarV1ReferenceBoolType
        , GrammarV1ReferenceBoundaryRequirement
            "B" (GrammarV1ReferencePrimitiveSpelling "U8")
        , GrammarV1ReferenceArchitectureRequirement
            "A" (GrammarV1ReferencePrimitiveSpelling "I16")
        , GrammarV1ReferenceEffectsRequirement
            "E" GrammarV1ReferenceEffectSetLiteral
        , GrammarV1ReferenceAuthorityRequirement
            (GrammarV1ReferencePrimitiveSpelling "F32")
        , GrammarV1ReferenceBoundaryRepresentationRequirement
            (GrammarV1ReferencePrimitiveSpelling "String")
        , GrammarV1ReferenceRepresentationRequirement
        , GrammarV1ReferencePlacementRequirement
        , GrammarV1ReferenceCostRequirement
        , GrammarV1ReferenceEnvironmentRequirement
        ]
  (referenceValues, productionValues) <-
    parseRequirementSpines "all-requirements" source
  case referenceValues of
    [actual]
      | actual /= expected -> Left
          ("all requirements -- expected exhaustive ordered alternatives\nexpected: "
            <> show expected <> "\nactual:   " <> show actual)
      | productionValues /= referenceValues -> Left
          ("all requirements -- certified/production mismatch\nreference: "
            <> show referenceValues <> "\nproduction: " <> show productionValues)
      | otherwise -> Right ()
    other -> Left
      ("all requirements -- expected one type alias, got " <> show (length other))

checkEffectReference :: Either String ()
checkEffectReference = do
  let source = "type EffectBound requires { effects E within Allowed; } = Unit;"
  (referenceValues, productionValues) <-
    parseRequirementSpines "effect-reference" source
  let expected =
        [[GrammarV1ReferenceEffectsRequirement
            "E" GrammarV1ReferenceEffectSetReference]]
  if referenceValues == expected && productionValues == referenceValues
    then Right ()
    else Left
      ("effect reference -- unexpected projection\nexpected: "
        <> show expected <> "\nreference: " <> show referenceValues
        <> "\nproduction: " <> show productionValues)

parseRequirementSpines
  :: String
  -> Text
  -> Either String
      ( [[GrammarV1ReferenceGenericRequirementSpine]]
      , [[GrammarV1ReferenceGenericRequirementSpine]]
      )
parseRequirementSpines label source = do
  sourceTokens <- mapLeft show
    (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show
    (grammarV1ReferenceTypeAliasRequirementSpines tree)
  production <- mapLeft show
    (parseGrammarV1StructuralSource (Text.pack label) source)
  pure
    ( referenceValues
    , grammarV1ProductionTypeAliasRequirementSpines production
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
          sourceTokens <- mapLeft show
            (lexGrammarV1SourceTokens sourceName source)
          tree <- mapLeft show
            (grammarV1ReferenceParseSourceTokens sourceTokens)
          referenceValues <- mapLeft show
            (grammarV1ReferenceTypeAliasRequirementSpines tree)
          production <- mapLeft show
            (parseGrammarV1StructuralSource sourceName source)
          let productionValues =
                grammarV1ProductionTypeAliasRequirementSpines production
          if referenceValues == productionValues
            then Right ()
            else Left
              (label <> " -- certified/production generic-requirement mismatch\nreference: "
                <> show referenceValues <> "\nproduction: " <> show productionValues)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
