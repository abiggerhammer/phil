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
    [ testIO "SURF-002 refinement callable fixture preserves contract shell and ensures"
        expectRefinementCallable
    , testIO "SURF-003 callable refinement missing bar rejects at syntax"
        (expectFixtureReject "rejected/01-refinement-missing-bar.phil")
    , test "SURF-002 unsupported valid callable clause fails closed"
        unsupportedCallableClauseFailsClosed
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectRefinementCallable :: IO (Either String ())
expectRefinementCallable = do
  parsed <- parseFixture "accepted/01-refinement-type.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ claimTop, Located _ callableTop] -> do
        case locatedValue (grammarV1Declaration claimTop) of
          GrammarV1ClaimDeclaration claimDecl -> do
            assert (locatedValue (grammarV1ClaimName claimDecl) == "Positive")
              "claim name was not Positive"
            case grammarV1ClaimProposition claimDecl of
              Just proposition -> assertNameIntegerRelation GrammarV1GreaterRelation "x" "0" proposition
              Nothing -> Left "Positive claim had no proposition"
          other -> Left ("expected claim first, got " <> show other)
        case locatedValue (grammarV1Declaration callableTop) of
          GrammarV1CallableContractDeclaration callableDecl -> do
            assert (locatedValue (grammarV1CallableName callableDecl) == "KeepPositive")
              "callable name was not KeepPositive"
            assert (null (grammarV1CallableGenericParams callableDecl))
              "unexpected callable generic parameters"
            assert (null (grammarV1CallableRequirements callableDecl))
              "unexpected callable generic requirements"
            case grammarV1CallableTermParams callableDecl of
              [Located _ param] -> do
                assert (locatedValue (grammarV1TermParamName param) == "x")
                  "callable parameter name was not x"
                assertRefinementParameter (locatedValue (grammarV1TermParamType param))
              params -> Left ("expected one callable parameter, got " <> show (length params))
            assert (locatedValue (grammarV1CallableResultType callableDecl) == GrammarV1UnsignedType "U32")
              "callable result type was not U32"
            case grammarV1CallableClauses callableDecl of
              [Located _ (GrammarV1CallableEnsures proposition)] ->
                assertNameIntegerRelation GrammarV1GreaterRelation "x" "0" proposition
              clauses -> Left ("expected one ensures clause, got " <> show clauses)
          other -> Left ("expected callable contract second, got " <> show other)
      declarations -> Left ("expected claim and callable declarations, got " <> show (length declarations))

assertRefinementParameter :: GrammarV1Type -> Either String ()
assertRefinementParameter ty = case ty of
  GrammarV1RefinementType binder baseType predicate -> do
    assert (locatedValue binder == "v") "refinement binder was not v"
    assert (locatedValue baseType == GrammarV1UnsignedType "U32")
      "refinement base type was not U32"
    assertNameIntegerRelation GrammarV1GreaterRelation "v" "0" predicate
  other -> Left ("expected refinement parameter type, got " <> show other)

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

unsupportedCallableClauseFailsClosed :: Either String ()
unsupportedCallableClauseFailsClosed =
  case parseGrammarV1StructuralSource "unsupported-callable-clause" source of
    Left _ -> Right ()
    Right value -> Left ("expected unsupported callable clause to fail closed, got " <> show value)
  where
    source = "callable C(x : U32) -> U32 { consumes { x }; }"

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
