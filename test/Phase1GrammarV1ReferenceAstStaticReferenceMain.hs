{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticArgumentTag (..)
  , GrammarV1ReferenceStaticReferenceSpine (..)
  , grammarV1ProductionTypeAliasStaticReferenceSpines
  , grammarV1ReferenceTypeAliasStaticReferenceSpines
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
  let directCases =
        [ ( "plain"
          , "type Plain = Foo.Bar;"
          , [[reference ["Foo", "Bar"] []]]
          )
        , ( "empty-static-args"
          , "type Empty = Foo[];"
          , [[reference ["Foo"] []]]
          )
        , ( "all-static-argument-categories"
          , "type Mixed = Foo[U8, end Done, true, {IO}];"
          , [[reference ["Foo"]
              [ GrammarV1ReferenceStaticTypeArgument
                  (GrammarV1ReferencePrimitiveSpelling "U8")
              , GrammarV1ReferenceStaticSessionArgument
              , GrammarV1ReferenceStaticValueArgument
              , GrammarV1ReferenceStaticEffectSetArgument
              ]]]
          )
        , ( "static-reference-as-static-value"
          , "type Generic[T : Type] = Box[T];"
          , [[reference ["Box"] [GrammarV1ReferenceStaticValueArgument]]]
          )
        , ( "frame-reference"
          , "type Framed = Frame[Codec[Unit, false]];"
          , [[reference ["Codec"]
              [ GrammarV1ReferenceStaticTypeArgument GrammarV1ReferenceUnitType
              , GrammarV1ReferenceStaticValueArgument
              ]]]
          )
        , ( "validated-reference"
          , "type Checked = Validated[Validator[U16], 1, 2];"
          , [[reference ["Validator"]
              [ GrammarV1ReferenceStaticTypeArgument
                  (GrammarV1ReferencePrimitiveSpelling "U16")
              ]]]
          )
        ]
      directResults =
        [ checkDirect label source expected
        | (label, source, expected) <- directCases
        ]
      directFailures = [detail | Left detail <- directResults]
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
          ("PASS: certified Grammar-v1 static-reference spine agrees with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

reference
  :: [Text]
  -> [GrammarV1ReferenceStaticArgumentTag]
  -> GrammarV1ReferenceStaticReferenceSpine
reference name arguments = GrammarV1ReferenceStaticReferenceSpine
  { grammarV1ReferenceStaticReferenceName = name
  , grammarV1ReferenceStaticReferenceArguments = arguments
  }

checkDirect
  :: String
  -> Text
  -> [[GrammarV1ReferenceStaticReferenceSpine]]
  -> Either String ()
checkDirect label source expected = do
  (referenceSpines, productionSpines) <- parseReferenceSpines label source
  if referenceSpines /= productionSpines
    then Left
      (label <> " -- certified/production static-reference mismatch\nreference: "
        <> show referenceSpines <> "\nproduction: " <> show productionSpines)
    else if referenceSpines /= expected
      then Left
        (label <> " -- unexpected static-reference projection\nexpected: "
          <> show expected <> "\nactual: " <> show referenceSpines)
      else Right ()

parseReferenceSpines
  :: String
  -> Text
  -> Either String
      ( [[GrammarV1ReferenceStaticReferenceSpine]]
      , [[GrammarV1ReferenceStaticReferenceSpine]]
      )
parseReferenceSpines label source = do
  sourceTokens <- mapLeft show
    (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceSpines <- mapLeft show
    (grammarV1ReferenceTypeAliasStaticReferenceSpines tree)
  production <- mapLeft show
    (parseGrammarV1StructuralSource (Text.pack label) source)
  pure
    ( referenceSpines
    , grammarV1ProductionTypeAliasStaticReferenceSpines production
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
          referenceSpines <- mapLeft show
            (grammarV1ReferenceTypeAliasStaticReferenceSpines tree)
          production <- mapLeft show
            (parseGrammarV1StructuralSource sourceName source)
          let productionSpines =
                grammarV1ProductionTypeAliasStaticReferenceSpines production
          if referenceSpines == productionSpines
            then Right ()
            else Left
              (label <> " -- certified/production static-reference mismatch\nreference: "
                <> show referenceSpines <> "\nproduction: " <> show productionSpines)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
