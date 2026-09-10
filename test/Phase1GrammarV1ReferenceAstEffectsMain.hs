{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstEffects
  ( GrammarV1ReferenceEffectSetSpine (..)
  , GrammarV1ReferenceEffectSpine (..)
  , grammarV1ProductionTypeAliasEffectSets
  , grammarV1ReferenceEffectSetSpine
  , grammarV1ReferenceTypeAliasEffectSets
  )
import Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceBinaryOperator (..)
  , GrammarV1ReferenceExpressionCore (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticArgumentTag (..)
  , GrammarV1ReferenceStaticReferenceSpine (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeTag (..)
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  , grammarV1ReferenceParseSourceTokens
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
        [ ( "empty-effect-set"
          , "type T requires { effects E within {}; } = U8;"
          , [[GrammarV1ReferenceEffectSetLiteral []]]
          )
        , ( "effect-labels-and-arguments"
          , "type T requires { effects E within {Read[U32](store), Write(store, x + 1)}; } = U8;"
          , [[ GrammarV1ReferenceEffectSetLiteral
                [ effect
                    (reference ["Read"]
                      [GrammarV1ReferenceStaticTypeArgument
                        (GrammarV1ReferencePrimitiveSpelling "U32")])
                    [name ["store"]]
                , effect
                    (reference ["Write"] [])
                    [ name ["store"]
                    , GrammarV1ReferenceBinaryExpression
                        (name ["x"])
                        GrammarV1ReferenceAdd
                        (GrammarV1ReferenceIntegerExpression "1")
                    ]
                ]
             ]]
          )
        , ( "effect-set-reference"
          , "type T requires { effects E within Pkg.Allowed[U8]; } = U8;"
          , [[ GrammarV1ReferenceEffectSetReference
                (reference ["Pkg", "Allowed"]
                  [GrammarV1ReferenceStaticTypeArgument
                    (GrammarV1ReferencePrimitiveSpelling "U8")])
             ]]
          )
        , ( "multiple-requirements-preserve-order"
          , "type T requires { effects E within {}; effects F within Allowed; } = U8;"
          , [[ GrammarV1ReferenceEffectSetLiteral []
             , GrammarV1ReferenceEffectSetReference (reference ["Allowed"] [])
             ]]
          )
        , ( "command-argument-boundary"
          , "type T requires { effects E within {Close(close endpoint)}; } = U8;"
          , [[ GrammarV1ReferenceEffectSetLiteral
                [ effect
                    (reference ["Close"] [])
                    [GrammarV1ReferenceCommandExpression "close_expression"]
                ]
             ]]
          )
        , ( "unicode-effect-subject"
          , "type T requires { effects E within {Μέτρηση(δοχείο)}; } = U8;"
          , [[ GrammarV1ReferenceEffectSetLiteral
                [effect (reference ["Μέτρηση"] []) [name ["δοχείο"]]]
             ]]
          )
        ]
      directResults =
        [ checkDirect label source expected
        | (label, source, expected) <- directCases
        ]
      malformedResult =
        case grammarV1ReferenceEffectSetSpine (GrammarV1ReferenceLiteral "{") of
          Left _ -> Right ()
          Right value -> Left
            ("malformed-tree -- non-effect-set root decoded as " <> show value)
      directFailures = [detail | Left detail <- malformedResult : directResults]
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
          ("PASS: certified Grammar-v1 effect sets agree with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

effect
  :: GrammarV1ReferenceStaticReferenceSpine
  -> [GrammarV1ReferenceExpressionCore]
  -> GrammarV1ReferenceEffectSpine
effect referenceValue arguments = GrammarV1ReferenceEffectSpine
  { grammarV1ReferenceEffectReference = referenceValue
  , grammarV1ReferenceEffectArguments = arguments
  }

name :: [Text] -> GrammarV1ReferenceExpressionCore
name parts = GrammarV1ReferenceNameExpression (reference parts []) []

reference
  :: [Text]
  -> [GrammarV1ReferenceStaticArgumentTag]
  -> GrammarV1ReferenceStaticReferenceSpine
reference parts arguments = GrammarV1ReferenceStaticReferenceSpine
  { grammarV1ReferenceStaticReferenceName = parts
  , grammarV1ReferenceStaticReferenceArguments = arguments
  }

checkDirect
  :: String
  -> Text
  -> [[GrammarV1ReferenceEffectSetSpine]]
  -> Either String ()
checkDirect label source expected = do
  (referenceValues, productionValues) <- parseValues label source
  if referenceValues /= productionValues
    then Left
      (label <> " -- certified/production effect-set mismatch\nreference: "
        <> show referenceValues <> "\nproduction: " <> show productionValues)
    else if referenceValues /= expected
      then Left
        (label <> " -- unexpected effect-set projection\nexpected: "
          <> show expected <> "\nactual: " <> show referenceValues)
      else Right ()

parseValues
  :: String
  -> Text
  -> Either String
      ( [[GrammarV1ReferenceEffectSetSpine]]
      , [[GrammarV1ReferenceEffectSetSpine]]
      )
parseValues label source = do
  sourceTokens <- mapLeft show
    (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show (grammarV1ReferenceTypeAliasEffectSets tree)
  production <- mapLeft show
    (parseGrammarV1StructuralSource (Text.pack label) source)
  pure
    ( referenceValues
    , grammarV1ProductionTypeAliasEffectSets production
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
            (grammarV1ReferenceTypeAliasEffectSets tree)
          production <- mapLeft show
            (parseGrammarV1StructuralSource sourceName source)
          let productionValues = grammarV1ProductionTypeAliasEffectSets production
          if referenceValues == productionValues
            then Right ()
            else Left
              (label <> " -- certified/production effect-set mismatch\nreference: "
                <> show referenceValues <> "\nproduction: " <> show productionValues)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
