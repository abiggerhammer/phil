{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-002 explicit transport preserves Bytes and Proof types"
        expectExplicitTransport
    , testIO "SURF-002 refinement transport preserves binder and predicate"
        expectRefinementTransport
    , testIO "SURF-003 transport missing using rejects at syntax"
        (expectFixtureReject "rejected/02-transport-missing-using.phil")
    , testIO "SURF-003 transport keyword order rejects at syntax"
        (expectFixtureReject "rejected/08-transport-wrong-keyword-order.phil")
    , test "SURF-003 refinement type missing bar rejects at syntax"
        refinementMissingBarRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectExplicitTransport :: IO (Either String ())
expectExplicitTransport = do
  parsed <- parseFixture "accepted/02-explicit-transport.phil"
  pure $ do
    component <- onlyComponent parsed
    params <- requireTwoParams component
    case params of
      [Located _ valueParam, Located _ equalityParam] -> do
        assertBytesNamed "n" (locatedValue (grammarV1TermParamType valueParam))
        assertProofRelation GrammarV1EqualRelation "n" "m"
          (locatedValue (grammarV1TermParamType equalityParam))
      _ -> Left "internal two-parameter assertion mismatch"
    transport <- onlyTransport component
    assertTransport "value" "m" "equality" transport

expectRefinementTransport :: IO (Either String ())
expectRefinementTransport = do
  parsed <- parseFixture "accepted/08-refinement-transport-composition.phil"
  pure $ do
    component <- onlyComponent parsed
    params <- requireTwoParams component
    case params of
      [Located _ valueParam, Located _ equalityParam] -> do
        case locatedValue (grammarV1TermParamType valueParam) of
          GrammarV1RefinementType binder baseType predicate -> do
            assert (locatedValue binder == "b") "refinement binder was not b"
            assertBytesNamed "n" (locatedValue baseType)
            assertRelation GrammarV1LessEqualRelation "n" "m" predicate
          other -> Left ("expected refinement type, got " <> show other)
        assertProofRelation GrammarV1EqualRelation "n" "m"
          (locatedValue (grammarV1TermParamType equalityParam))
      _ -> Left "internal two-parameter assertion mismatch"
    transport <- onlyTransport component
    assertTransport "value" "m" "equality" transport

onlyComponent
  :: Either GrammarV1ParseDiagnostic GrammarV1SourceFile
  -> Either String GrammarV1ComponentDecl
onlyComponent parsed = do
  sourceFile <- mapLeft show parsed
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration component -> Right component
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

requireTwoParams
  :: GrammarV1ComponentDecl
  -> Either String [Located GrammarV1TermParam]
requireTwoParams component = case grammarV1ComponentTermParams component of
  Just params@[_, _] -> Right params
  other -> Left ("expected exactly two parameters, got " <> show other)

onlyTransport
  :: GrammarV1ComponentDecl
  -> Either String GrammarV1Expression
onlyTransport component =
  case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
    [Located _ (GrammarV1ExpressionStatement (Located _ expression))] ->
      case expression of
        GrammarV1TransportExpression _ _ _ -> Right expression
        other -> Left ("expected transport expression, got " <> show other)
    statements -> Left ("expected one expression statement, got " <> show (length statements))

assertTransport
  :: Text.Text
  -> Text.Text
  -> Text.Text
  -> GrammarV1Expression
  -> Either String ()
assertTransport valueName targetLength evidenceName expression = case expression of
  GrammarV1TransportExpression value target evidence -> do
    assertName valueName value
    assertBytesNamed targetLength (locatedValue target)
    assertName evidenceName evidence
  other -> Left ("expected transport expression, got " <> show other)

assertProofRelation
  :: GrammarV1RelationOperator
  -> Text.Text
  -> Text.Text
  -> GrammarV1Type
  -> Either String ()
assertProofRelation operator leftName rightName ty = case ty of
  GrammarV1ProofType proposition -> assertRelation operator leftName rightName proposition
  other -> Left ("expected Proof type, got " <> show other)

assertRelation
  :: GrammarV1RelationOperator
  -> Text.Text
  -> Text.Text
  -> Located GrammarV1Proposition
  -> Either String ()
assertRelation expectedOperator leftName rightName (Located _ proposition) = case proposition of
  GrammarV1RelationProposition left operator right -> do
    assert (locatedValue operator == expectedOperator)
      ("unexpected relation operator " <> show (locatedValue operator))
    assertName leftName left
    assertName rightName right
  other -> Left ("expected relation proposition, got " <> show other)

assertBytesNamed :: Text.Text -> GrammarV1Type -> Either String ()
assertBytesNamed expected ty = case ty of
  GrammarV1BytesType lengthExpression -> assertName expected lengthExpression
  other -> Left ("expected Bytes type, got " <> show other)

assertName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertName expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected name " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "unexpected static arguments on simple name"
    assert (null arguments) "unexpected term arguments on simple name"
  other -> Left ("expected simple name expression, got " <> show other)

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

refinementMissingBarRejects :: Either String ()
refinementMissingBarRejects =
  case parseGrammarV1StructuralSource "bad-refinement" source of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)
  where
    source = "component Bad(x : {v : U32 v > 0}) {}"

parseFixture
  :: FilePath
  -> IO (Either GrammarV1ParseDiagnostic GrammarV1SourceFile)
parseFixture relativePath = do
  let path = "test/fixtures/phase1-surface/" <> relativePath
  source <- TextIO.readFile path
  pure (parseGrammarV1StructuralSource (Text.pack relativePath) source)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
