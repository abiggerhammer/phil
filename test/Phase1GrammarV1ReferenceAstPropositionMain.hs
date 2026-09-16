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
  , GrammarV1ReferenceShiftOperator (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore (..)
  , GrammarV1ReferenceRelationOperator (..)
  , GrammarV1ReferenceTypeAliasPropositions (..)
  , grammarV1ProductionTypeAliasPropositions
  , grammarV1ReferencePropositionCore
  , grammarV1ReferenceTypeAliasPropositions
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
        [ ( "boolean-precedence"
          , "type T = Proof[not false and true or false];"
          , [ surface []
                [ orP
                    (andP (notP falseP) trueP)
                    falseP
                ]
            ]
          )
        , ( "parentheses-normalize"
          , "type T = Proof[(true or false) and true];"
          , [surface [] [andP (orP trueP falseP) trueP]]
          )
        , ( "relation-shift-operands"
          , "type T = Proof[a << 1 == b >> 2];"
          , [ surface []
                [ relation
                    (shiftE (name ["a"]) GrammarV1ReferenceShiftLeft (integer "1"))
                    GrammarV1ReferenceEqualRelation
                    (shiftE (name ["b"]) GrammarV1ReferenceShiftRight (integer "2"))
                ]
            ]
          )
        , ( "claim-application"
          , "type T = Proof[Pred[U8](x + 1, true)];"
          , [ surface []
                [ GrammarV1ReferenceClaimApplicationProposition
                    (reference
                      ["Pred"]
                      [ GrammarV1ReferenceStaticTypeArgument
                          (GrammarV1ReferencePrimitiveSpelling "U8")
                      ])
                    [ binaryE (name ["x"]) GrammarV1ReferenceAdd (integer "1")
                    , GrammarV1ReferenceBoolExpression True
                    ]
                ]
            ]
          )
        , ( "all-relations"
          , Text.unlines
              [ "type R0 = Proof[a == b];"
              , "type R1 = Proof[a != b];"
              , "type R2 = Proof[a <= b];"
              , "type R3 = Proof[a >= b];"
              , "type R4 = Proof[a < b];"
              , "type R5 = Proof[a > b];"
              , "type R6 = Proof[a in b];"
              , "type R7 = Proof[a disjoint b];"
              ]
          , map (surface [] . pure)
              [ relation (name ["a"]) GrammarV1ReferenceEqualRelation (name ["b"])
              , relation (name ["a"]) GrammarV1ReferenceNotEqualRelation (name ["b"])
              , relation (name ["a"]) GrammarV1ReferenceLessEqualRelation (name ["b"])
              , relation (name ["a"]) GrammarV1ReferenceGreaterEqualRelation (name ["b"])
              , relation (name ["a"]) GrammarV1ReferenceLessRelation (name ["b"])
              , relation (name ["a"]) GrammarV1ReferenceGreaterRelation (name ["b"])
              , relation (name ["a"]) GrammarV1ReferenceInRelation (name ["b"])
              , relation (name ["a"]) GrammarV1ReferenceDisjointRelation (name ["b"])
              ]
          )
        , ( "requirement-propositions"
          , Text.unlines
              [ "type T requires {"
              , "  proposition true;"
              , "  representation not false;"
              , "  placement x == y;"
              , "  cost Pred();"
              , "  environment true or false;"
              , "} = Unit;"
              ]
          , [ surface
                [ trueP
                , notP falseP
                , relation (name ["x"]) GrammarV1ReferenceEqualRelation (name ["y"])
                , GrammarV1ReferenceClaimApplicationProposition (reference ["Pred"] []) []
                , orP trueP falseP
                ]
                []
            ]
          )
        ]
      directResults =
        [ checkDirect label source expected
        | (label, source, expected) <- directCases
        ]
      malformedResult =
        case grammarV1ReferencePropositionCore (GrammarV1ReferenceLiteral "true") of
          Left _ -> Right ()
          Right value -> Left
            ("malformed-tree -- non-proposition root decoded as " <> show value)
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
          ("PASS: certified Grammar-v1 proposition structure agrees with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

surface
  :: [GrammarV1ReferencePropositionCore]
  -> [GrammarV1ReferencePropositionCore]
  -> GrammarV1ReferenceTypeAliasPropositions
surface requirements targets = GrammarV1ReferenceTypeAliasPropositions
  { grammarV1ReferenceTypeAliasRequirementPropositions = requirements
  , grammarV1ReferenceTypeAliasTargetPropositions = targets
  }

trueP :: GrammarV1ReferencePropositionCore
trueP = GrammarV1ReferenceTrueProposition

falseP :: GrammarV1ReferencePropositionCore
falseP = GrammarV1ReferenceFalseProposition

notP :: GrammarV1ReferencePropositionCore -> GrammarV1ReferencePropositionCore
notP = GrammarV1ReferenceNotProposition

andP
  :: GrammarV1ReferencePropositionCore
  -> GrammarV1ReferencePropositionCore
  -> GrammarV1ReferencePropositionCore
andP = GrammarV1ReferenceAndProposition

orP
  :: GrammarV1ReferencePropositionCore
  -> GrammarV1ReferencePropositionCore
  -> GrammarV1ReferencePropositionCore
orP = GrammarV1ReferenceOrProposition

relation
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceRelationOperator
  -> GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferencePropositionCore
relation = GrammarV1ReferenceRelationProposition

integer :: Text -> GrammarV1ReferenceExpressionCore
integer = GrammarV1ReferenceIntegerExpression

name :: [Text] -> GrammarV1ReferenceExpressionCore
name parts = GrammarV1ReferenceNameExpression (reference parts []) []

binaryE
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceBinaryOperator
  -> GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceExpressionCore
binaryE = GrammarV1ReferenceBinaryExpression

shiftE
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceShiftOperator
  -> GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceExpressionCore
shiftE = GrammarV1ReferenceShiftExpression

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
  -> [GrammarV1ReferenceTypeAliasPropositions]
  -> Either String ()
checkDirect label source expected = do
  (referenceValues, productionValues) <- parseValues label source
  if referenceValues /= productionValues
    then Left
      (label <> " -- certified/production proposition mismatch\nreference: "
        <> show referenceValues <> "\nproduction: " <> show productionValues)
    else if referenceValues /= expected
      then Left
        (label <> " -- unexpected proposition projection\nexpected: "
          <> show expected <> "\nactual: " <> show referenceValues)
      else Right ()

parseValues
  :: String
  -> Text
  -> Either String
      ( [GrammarV1ReferenceTypeAliasPropositions]
      , [GrammarV1ReferenceTypeAliasPropositions]
      )
parseValues label source = do
  sourceTokens <- mapLeft show
    (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show
    (grammarV1ReferenceTypeAliasPropositions tree)
  production <- mapLeft show
    (parseGrammarV1StructuralSource (Text.pack label) source)
  pure
    ( referenceValues
    , grammarV1ProductionTypeAliasPropositions production
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
            (grammarV1ReferenceTypeAliasPropositions tree)
          production <- mapLeft show
            (parseGrammarV1StructuralSource sourceName source)
          let productionValues = grammarV1ProductionTypeAliasPropositions production
          if referenceValues == productionValues
            then Right ()
            else Left
              (label <> " -- certified/production proposition mismatch\nreference: "
                <> show referenceValues <> "\nproduction: " <> show productionValues)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
