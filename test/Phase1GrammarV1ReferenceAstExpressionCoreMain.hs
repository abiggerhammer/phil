{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceBinaryOperator (..)
  , GrammarV1ReferenceExpressionCore (..)
  , GrammarV1ReferenceFailureTarget (..)
  , GrammarV1ReferenceFallbackCore (..)
  , GrammarV1ReferenceShiftOperator (..)
  , grammarV1ProductionTypeAliasExpressionCores
  , grammarV1ReferenceExpressionCore
  , grammarV1ReferenceTypeAliasExpressionCores
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
        [ ( "literal-leaves"
          , Text.unlines
              [ "type B0 = Bytes[true];"
              , "type B1 = Bytes[false];"
              , "type B2 = Bytes[unit];"
              , "type B3 = Bytes['λ'];"
              , "type B4 = Bytes[\"hé🙂\"];"
              , "type B5 = Bytes[1.25];"
              , "type B6 = Bytes[7];"
              ]
          , [ [GrammarV1ReferenceBoolExpression True]
            , [GrammarV1ReferenceBoolExpression False]
            , [GrammarV1ReferenceUnitExpression]
            , [GrammarV1ReferenceCharExpression "λ"]
            , [GrammarV1ReferenceStringExpression "hé🙂"]
            , [GrammarV1ReferenceFloatExpression "1.25"]
            , [GrammarV1ReferenceIntegerExpression "7"]
            ]
          )
        , ( "precedence"
          , "type T = Bytes[-1 + 8 / 3 % 2 * 4 << 2 - 1];"
          , [[ shift
                (binary
                  (negateValue (integer "1"))
                  GrammarV1ReferenceAdd
                  (binary
                    (binary
                      (binary (integer "8") GrammarV1ReferenceDivide (integer "3"))
                      GrammarV1ReferenceRemainder
                      (integer "2"))
                    GrammarV1ReferenceMultiply
                    (integer "4")))
                GrammarV1ReferenceShiftLeft
                (binary (integer "2") GrammarV1ReferenceSubtract (integer "1"))
             ]]
          )
        , ( "name-call-projection"
          , "type T = Bytes[Pkg.F[U32](x, y + 1).field];"
          , [[ GrammarV1ReferenceProjectionExpression
                (GrammarV1ReferenceNameExpression
                  (reference
                    ["Pkg", "F"]
                    [GrammarV1ReferenceStaticTypeArgument
                      (GrammarV1ReferencePrimitiveSpelling "U32")])
                  [ name ["x"] [] []
                  , binary (name ["y"] [] []) GrammarV1ReferenceAdd (integer "1")
                  ])
                "field"
             ]]
          )
        , ( "tuple-parentheses"
          , "type T = Bytes[(x, (y + 1), \"z\")];"
          , [[ GrammarV1ReferenceTupleExpression
                [ name ["x"] [] []
                , GrammarV1ReferenceParenthesizedExpression
                    (binary (name ["y"] [] []) GrammarV1ReferenceAdd (integer "1"))
                , GrammarV1ReferenceStringExpression "z"
                ]
             ]]
          )
        , ( "fallback-fail"
          , "type T = Bytes[x or fail Err[U8](code)];"
          , [[ GrammarV1ReferenceFallbackExpression
                (name ["x"] [] [])
                (GrammarV1ReferenceFailFallback GrammarV1ReferenceFailureTarget
                  { grammarV1ReferenceFailureTargetReference =
                      reference
                        ["Err"]
                        [GrammarV1ReferenceStaticTypeArgument
                          (GrammarV1ReferencePrimitiveSpelling "U8")]
                  , grammarV1ReferenceFailureTargetArguments =
                      [name ["code"] [] []]
                  })
             ]]
          )
        , ( "fallback-reject"
          , "type T = Bytes[x or reject y + 1];"
          , [[ GrammarV1ReferenceFallbackExpression
                (name ["x"] [] [])
                (GrammarV1ReferenceRejectFallback
                  (binary (name ["y"] [] []) GrammarV1ReferenceAdd (integer "1")))
             ]]
          )
        , ( "command-family-boundary"
          , "type T = Bytes[close x];"
          , [[GrammarV1ReferenceCommandExpression "close_expression"]]
          )
        , ( "validated-expression-holes"
          , "type T = Validated[Check, payload + 1, (proofValue)];"
          , [[ binary (name ["payload"] [] []) GrammarV1ReferenceAdd (integer "1")
             , GrammarV1ReferenceParenthesizedExpression (name ["proofValue"] [] [])
             ]]
          )
        ]
      directResults =
        [ checkDirect label source expected
        | (label, source, expected) <- directCases
        ]
      malformedResult =
        case grammarV1ReferenceExpressionCore (GrammarV1ReferenceLiteral "true") of
          Left _ -> Right ()
          Right value -> Left
            ("malformed-tree -- non-expression root decoded as " <> show value)
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
          ("PASS: certified Grammar-v1 ordinary expression core agrees with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

integer :: Text -> GrammarV1ReferenceExpressionCore
integer = GrammarV1ReferenceIntegerExpression

negateValue :: GrammarV1ReferenceExpressionCore -> GrammarV1ReferenceExpressionCore
negateValue = GrammarV1ReferenceNegateExpression

binary
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceBinaryOperator
  -> GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceExpressionCore
binary = GrammarV1ReferenceBinaryExpression

shift
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceShiftOperator
  -> GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceExpressionCore
shift = GrammarV1ReferenceShiftExpression

name
  :: [Text]
  -> [GrammarV1ReferenceStaticArgumentTag]
  -> [GrammarV1ReferenceExpressionCore]
  -> GrammarV1ReferenceExpressionCore
name parts staticArguments termArguments =
  GrammarV1ReferenceNameExpression
    (reference parts staticArguments)
    termArguments

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
  -> [[GrammarV1ReferenceExpressionCore]]
  -> Either String ()
checkDirect label source expected = do
  (referenceValues, productionValues) <- parseValues label source
  if referenceValues /= productionValues
    then Left
      (label <> " -- certified/production expression-core mismatch\nreference: "
        <> show referenceValues <> "\nproduction: " <> show productionValues)
    else if referenceValues /= expected
      then Left
        (label <> " -- unexpected expression-core projection\nexpected: "
          <> show expected <> "\nactual: " <> show referenceValues)
      else Right ()

parseValues
  :: String
  -> Text
  -> Either String
      ( [[GrammarV1ReferenceExpressionCore]]
      , [[GrammarV1ReferenceExpressionCore]]
      )
parseValues label source = do
  sourceTokens <- mapLeft show
    (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show
    (grammarV1ReferenceTypeAliasExpressionCores tree)
  production <- mapLeft show
    (parseGrammarV1StructuralSource (Text.pack label) source)
  pure
    ( referenceValues
    , grammarV1ProductionTypeAliasExpressionCores production
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
            (grammarV1ReferenceTypeAliasExpressionCores tree)
          production <- mapLeft show
            (parseGrammarV1StructuralSource sourceName source)
          let productionValues = grammarV1ProductionTypeAliasExpressionCores production
          if referenceValues == productionValues
            then Right ()
            else Left
              (label <> " -- certified/production expression-core mismatch\nreference: "
                <> show referenceValues <> "\nproduction: " <> show productionValues)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
