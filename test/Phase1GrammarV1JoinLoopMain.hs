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
    [ testIO "SURF-002 join invariant fixture preserves typed join state and invariant"
        expectJoinInvariant
    , testIO "SURF-002 typed loop state fixture preserves initializer invariant and continue"
        expectTypedLoopState
    , testIO "SURF-003 join invariant missing proposition rejects at syntax"
        (expectFixtureReject "rejected/18-join-invariant-missing-proposition.phil")
    , testIO "SURF-003 typed loop state missing initializer rejects at syntax"
        (expectFixtureReject "rejected/19-loop-typed-state-missing-initializer.phil")
    , test "SURF-002 untyped loop state and zero-actual continue are preserved"
        untypedLoopAndZeroContinuePreserved
    , test "SURF-003 loop state bindings reject trailing comma"
        loopStateTrailingCommaRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectJoinInvariant :: IO (Either String ())
expectJoinInvariant = do
  parsed <- parseFixture "accepted/23-join-invariant.phil"
  pure $ do
    expression <- singleComponentExpression =<< mapLeft show parsed
    case expression of
      GrammarV1IfExpression condition (Just joinClause) thenBlock (Just elseBlock) -> do
        assert (locatedValue condition == GrammarV1BoolExpression True)
          "if condition was not true"
        case grammarV1JoinState (locatedValue joinClause) of
          [Located _ slot] -> do
            assert (locatedValue (grammarV1StateSlotName slot) == "x_next")
              "join state slot name was not x_next"
            assert (locatedValue (grammarV1StateSlotType slot) == GrammarV1UnsignedType "U32")
              "join state slot type was not U32"
          slots -> Left ("expected one join state slot, got " <> show (length slots))
        case grammarV1JoinInvariant (locatedValue joinClause) of
          Just invariant -> assertNameIntegerRelation GrammarV1GreaterEqualRelation "x_next" "0" invariant
          Nothing -> Left "join invariant was missing"
        assertSingleExpressionName "x" thenBlock
        assertSingleExpressionName "x" elseBlock
      other -> Left ("expected if expression with join and else, got " <> show other)

expectTypedLoopState :: IO (Either String ())
expectTypedLoopState = do
  parsed <- parseFixture "accepted/24-typed-loop-state.phil"
  pure $ do
    expression <- singleComponentExpression =<< mapLeft show parsed
    case expression of
      GrammarV1LoopExpression [Located _ binding] (Just invariant) body -> do
        assert (locatedValue (grammarV1StateBindingName binding) == "i")
          "loop state binding name was not i"
        assert (fmap locatedValue (grammarV1StateBindingType binding) == Just (GrammarV1UnsignedType "U32"))
          "loop state binding type was not U32"
        assertSimpleName "n" (grammarV1StateBindingInitializer binding)
        assertNameIntegerRelation GrammarV1GreaterEqualRelation "i" "0" invariant
        case grammarV1BlockStatements (locatedValue body) of
          [Located _ (GrammarV1ExpressionStatement (Located _ (GrammarV1ContinueExpression [actual])))] ->
            assertSimpleName "i" actual
          statements -> Left ("expected continue(i) loop body, got " <> show statements)
      other -> Left ("expected typed loop expression, got " <> show other)

untypedLoopAndZeroContinuePreserved :: Either String ()
untypedLoopAndZeroContinuePreserved = do
  expression <- singleComponentExpression =<< mapLeft show
    (parseGrammarV1StructuralSource "untyped-loop" source)
  case expression of
    GrammarV1LoopExpression [Located _ binding] Nothing body -> do
      assert (grammarV1StateBindingType binding == Nothing)
        "untyped loop state unexpectedly acquired a type"
      assertSimpleName "n" (grammarV1StateBindingInitializer binding)
      case grammarV1BlockStatements (locatedValue body) of
        [Located _ (GrammarV1ExpressionStatement (Located _ (GrammarV1ContinueExpression [])))] -> Right ()
        statements -> Left ("expected zero-actual continue, got " <> show statements)
    other -> Left ("expected untyped loop expression, got " <> show other)
  where
    source = "component C(n : U32) { loop state (i = n) { continue; }; }"

loopStateTrailingCommaRejects :: Either String ()
loopStateTrailingCommaRejects =
  expectReject "component C(n : U32) { loop state (i = n,) { continue; }; }"

singleComponentExpression :: GrammarV1SourceFile -> Either String GrammarV1Expression
singleComponentExpression sourceFile = case grammarV1TopLevelDecls sourceFile of
  [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ComponentDeclaration componentDecl ->
      case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
        [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
        statements -> Left ("expected one component expression statement, got " <> show statements)
    other -> Left ("expected component declaration, got " <> show other)
  declarations -> Left ("expected one top-level declaration, got " <> show (length declarations))

assertSingleExpressionName :: Text.Text -> Located GrammarV1Block -> Either String ()
assertSingleExpressionName expected block =
  case grammarV1BlockStatements (locatedValue block) of
    [Located _ (GrammarV1ExpressionStatement expression)] -> assertSimpleName expected expression
    statements -> Left ("expected one expression statement, got " <> show statements)

assertNameIntegerRelation
  :: GrammarV1RelationOperator
  -> Text.Text
  -> Text.Text
  -> Located GrammarV1Proposition
  -> Either String ()
assertNameIntegerRelation expectedOperator expectedName expectedInteger (Located _ proposition) =
  case proposition of
    GrammarV1RelationProposition left operator right -> do
      assert (locatedValue operator == expectedOperator)
        ("unexpected relation operator " <> show (locatedValue operator))
      assertSimpleName expectedName left
      case locatedValue right of
        GrammarV1IntegerExpression value ->
          assert (value == expectedInteger)
            ("expected integer " <> Text.unpack expectedInteger <> ", got " <> Text.unpack value)
        other -> Left ("expected integer expression, got " <> show other)
    other -> Left ("expected relation proposition, got " <> show other)

assertSimpleName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertSimpleName expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected simple name " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "simple name unexpectedly had static arguments"
    assert (null arguments) "simple name unexpectedly had term arguments"
  other -> Left ("expected simple name expression, got " <> show other)

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "join-loop-negative" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

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
