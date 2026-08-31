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
    [ testIO "SURF-002 explicit linear closure fixture preserves exact syntax"
        expectExplicitLinearClosure
    , testIO "SURF-003 closure mode missing literal rejects at syntax"
        (expectFixtureReject "rejected/17-closure-mode-missing-literal.phil")
    , test "SURF-002 closure may omit mode and captures clauses"
        omittedModeAndCapturesPreserved
    , test "SURF-002 closure preserves nonempty captures in source order"
        nonemptyCapturesPreserved
    , test "SURF-003 closure captures reject trailing comma"
        captureTrailingCommaRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectExplicitLinearClosure :: IO (Either String ())
expectExplicitLinearClosure = do
  parsed <- parseFixture "accepted/22-closure-explicit-mode.phil"
  pure $ do
    closure <- componentClosure =<< mapLeft show parsed
    assert (grammarV1ClosureMode closure == Just GrammarV1Linear)
      "closure mode was not exact linear"
    case grammarV1ClosureTermParams closure of
      [Located _ param] -> do
        assert (locatedValue (grammarV1TermParamName param) == "x")
          "closure parameter name was not x"
        assert (locatedValue (grammarV1TermParamType param) == GrammarV1UnsignedType "U32")
          "closure parameter type was not U32"
      params -> Left ("expected one closure parameter, got " <> show params)
    assertNamedType "OneShot" (grammarV1ClosureSatisfies closure)
    case grammarV1ClosureCaptures closure of
      Just [] -> Right ()
      other -> Left ("expected explicit empty captures, got " <> show other)
    assertBlockReturnsName "x" (grammarV1ClosureBody closure)

omittedModeAndCapturesPreserved :: Either String ()
omittedModeAndCapturesPreserved = do
  closure <- componentClosure =<< mapLeft show
    (parseGrammarV1StructuralSource "closure-omitted" source)
  assert (grammarV1ClosureMode closure == Nothing)
    "omitted closure mode was not preserved"
  assert (grammarV1ClosureCaptures closure == Nothing)
    "absent captures clause was not preserved"
  where
    source = Text.unlines
      [ "component C() {"
      , "  closure (x : U32) satisfies OneShot { return x; };"
      , "}"
      ]

nonemptyCapturesPreserved :: Either String ()
nonemptyCapturesPreserved = do
  closure <- componentClosure =<< mapLeft show
    (parseGrammarV1StructuralSource "closure-captures" source)
  case grammarV1ClosureCaptures closure of
    Just captures ->
      assert (map locatedValue captures == ["a", "b"])
        ("unexpected capture list " <> show (map locatedValue captures))
    Nothing -> Left "expected explicit captures clause"
  where
    source = Text.unlines
      [ "component C(a : U32, b : U32) {"
      , "  closure () satisfies OneShot captures (a, b) { return a; };"
      , "}"
      ]

captureTrailingCommaRejects :: Either String ()
captureTrailingCommaRejects =
  expectReject "component C(a : U32) { closure () satisfies OneShot captures (a,) { return a; } }"

componentClosure :: GrammarV1SourceFile -> Either String GrammarV1Closure
componentClosure sourceFile =
  case reverse (grammarV1TopLevelDecls sourceFile) of
    Located _ topLevel : _ -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
          [Located _ (GrammarV1LetStatement _ initializer)] -> closureFromExpression initializer
          [Located _ (GrammarV1ExpressionStatement expression)] -> closureFromExpression expression
          statements -> Left ("expected one closure-bearing statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    [] -> Left "expected at least one top-level declaration"

closureFromExpression :: Located GrammarV1Expression -> Either String GrammarV1Closure
closureFromExpression (Located _ expression) = case expression of
  GrammarV1ClosureExpression closure -> Right closure
  other -> Left ("expected closure expression, got " <> show other)

assertNamedType :: Text.Text -> Located GrammarV1Type -> Either String ()
assertNamedType expected (Located _ ty) = case ty of
  GrammarV1NamedType reference ->
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected named type " <> Text.unpack expected)
  other -> Left ("expected named type, got " <> show other)

assertBlockReturnsName :: Text.Text -> Located GrammarV1Block -> Either String ()
assertBlockReturnsName expected (Located _ block) =
  case grammarV1BlockStatements block of
    [Located _ (GrammarV1ReturnStatement expression)] -> assertSimpleName expected expression
    statements -> Left ("expected one return statement, got " <> show statements)

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

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "closure-negative" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
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
