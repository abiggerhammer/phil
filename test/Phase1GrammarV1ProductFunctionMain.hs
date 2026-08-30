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
    [ testIO "SURF-002 product fixture preserves tuple types values and function shell"
        expectProductFixture
    , testIO "SURF-003 tuple type trailing comma rejects at syntax"
        (expectFixtureReject "rejected/16-tuple-type-trailing-comma.phil")
    , test "SURF-002 parenthesized expression remains distinct from tuple expression"
        parenthesizedExpressionPreserved
    , test "SURF-002 recursive function marker is preserved"
        recursiveFunctionPreserved
    , test "SURF-003 tuple expression trailing comma rejects at syntax"
        tupleExpressionTrailingCommaRejects
    , test "SURF-002 tuple and record patterns preserve recursive structure"
        tupleRecordPatternsPreserved
    , test "SURF-003 malformed tuple and record patterns reject at syntax"
        tupleRecordPatternsRejectMalformed
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectProductFixture :: IO (Either String ())
expectProductFixture = do
  parsed <- parseFixture "accepted/20-product-type-value.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ callableTop, Located _ functionTop] -> do
        checkCallable (locatedValue (grammarV1Declaration callableTop))
        checkFunction (locatedValue (grammarV1Declaration functionTop))
      declarations -> Left ("expected callable and function declarations, got " <> show (length declarations))

checkCallable :: GrammarV1Declaration -> Either String ()
checkCallable declaration = case declaration of
  GrammarV1CallableContractDeclaration callableDecl -> do
    assert (locatedValue (grammarV1CallableName callableDecl) == "MakePair")
      "callable name was not MakePair"
    assertTupleType (grammarV1CallableResultType callableDecl)
    case grammarV1CallableClauses callableDecl of
      [ Located _ (GrammarV1CallableOutcomes [Located _ spec])
        , Located _ (GrammarV1CallableOutcomeResidue residue)
        ] -> do
          assert (locatedValue (grammarV1OutcomeSpecKind spec) == GrammarV1SuccessOutcome)
            "outcome set did not preserve success kind"
          assertTupleType (grammarV1OutcomeSpecType spec)
          let residueValue = locatedValue residue
          assert (locatedValue (grammarV1OutcomeResidueKind residueValue) == GrammarV1SuccessOutcome)
            "outcome residue did not preserve success kind"
          assertTupleType (grammarV1OutcomeResidueType residueValue)
          case grammarV1OutcomeResidueClauses residueValue of
            [ Located _ (GrammarV1OutcomeState [])
              , Located _ (GrammarV1OutcomeCallee transition)
              ] -> assert (locatedValue transition == GrammarV1CalleePreserve)
                    "product outcome residue did not preserve callee"
            clauses -> Left ("unexpected product residue clauses " <> show clauses)
      clauses -> Left ("unexpected product callable clauses " <> show clauses)
  other -> Left ("expected callable declaration, got " <> show other)

checkFunction :: GrammarV1Declaration -> Either String ()
checkFunction declaration = case declaration of
  GrammarV1FunctionDeclaration functionDecl -> do
    assert (not (grammarV1FunctionRecursive functionDecl))
      "make_pair unexpectedly parsed as recursive"
    assert (locatedValue (grammarV1FunctionName functionDecl) == "make_pair")
      "function name was not make_pair"
    assert (null (grammarV1FunctionGenericParams functionDecl))
      "unexpected function generic parameters"
    assert (null (grammarV1FunctionRequirements functionDecl))
      "unexpected function generic requirements"
    assert (null (grammarV1FunctionTermParams functionDecl))
      "unexpected function term parameters"
    case grammarV1FunctionResultType functionDecl of
      Just resultType -> assertTupleType resultType
      Nothing -> Left "make_pair lost its result type"
    assertNamedType "MakePair" (grammarV1FunctionSatisfies functionDecl)
    case grammarV1BlockStatements (locatedValue (grammarV1FunctionBody functionDecl)) of
      [Located _ (GrammarV1ReturnStatement expression)] -> assertTupleValue expression
      statements -> Left ("expected one return statement, got " <> show statements)
  other -> Left ("expected function declaration, got " <> show other)

assertTupleType :: Located GrammarV1Type -> Either String ()
assertTupleType (Located _ ty) = case ty of
  GrammarV1TupleType [Located _ left, Located _ right] -> do
    assert (left == GrammarV1UnsignedType "U32") "tuple left type was not U32"
    assert (right == GrammarV1BoolType) "tuple right type was not Bool"
  other -> Left ("expected (U32, Bool) tuple type, got " <> show other)

assertTupleValue :: Located GrammarV1Expression -> Either String ()
assertTupleValue (Located _ expression) = case expression of
  GrammarV1TupleExpression [Located _ left, Located _ right] -> do
    assert (left == GrammarV1IntegerExpression "1") "tuple left value was not 1"
    assert (right == GrammarV1BoolExpression True) "tuple right value was not true"
  other -> Left ("expected (1, true) tuple expression, got " <> show other)

assertNamedType :: Text.Text -> Located GrammarV1Type -> Either String ()
assertNamedType expected (Located _ ty) = case ty of
  GrammarV1NamedType reference -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected named type " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "unexpected static arguments on named type"
  other -> Left ("expected named type, got " <> show other)

parenthesizedExpressionPreserved :: Either String ()
parenthesizedExpressionPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "parenthesized-expression" source
  functionDecl <- onlyFunction sourceFile
  case grammarV1BlockStatements (locatedValue (grammarV1FunctionBody functionDecl)) of
    [Located _ (GrammarV1ReturnStatement (Located _ expression))] ->
      case expression of
        GrammarV1ParenthesizedExpression inner ->
          assertSimpleName "x" inner
        other -> Left ("expected parenthesized expression, got " <> show other)
    statements -> Left ("expected one return statement, got " <> show statements)
  where
    source = "fn identity(x : U32) -> U32 satisfies Identity { return (x) }"

recursiveFunctionPreserved :: Either String ()
recursiveFunctionPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "recursive-function" source
  functionDecl <- onlyFunction sourceFile
  assert (grammarV1FunctionRecursive functionDecl) "recursive marker was not preserved"
  where
    source = "recursive fn recur(x : U32) -> U32 satisfies Rec { return x }"

tupleExpressionTrailingCommaRejects :: Either String ()
tupleExpressionTrailingCommaRejects =
  case parseGrammarV1StructuralSource "tuple-expression-trailing-comma" source of
    Left _ -> Right ()
    Right value -> Left ("expected tuple expression trailing comma rejection, got " <> show value)
  where
    source = "fn bad() -> (U32, Bool) satisfies Pair { return (1, true,) }"

tupleRecordPatternsPreserved :: Either String ()
tupleRecordPatternsPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "tuple-record-patterns" source
  functionDecl <- onlyFunction sourceFile
  case grammarV1BlockStatements (locatedValue (grammarV1FunctionBody functionDecl)) of
    [ Located _ (GrammarV1LetStatement tuplePattern tupleValue)
      , Located _ (GrammarV1LetStatement recordPattern recordValue)
      , Located _ (GrammarV1ReturnStatement result)
      ] -> do
        case locatedValue tuplePattern of
          GrammarV1TuplePattern
            [ left
              , Located _ (GrammarV1TuplePattern [middle, right])
              ] -> do
                assertIdentifierPattern "left" left
                assertIdentifierPattern "middle" middle
                assertIdentifierPattern "right" right
          other -> Left ("unexpected recursive tuple pattern " <> show other)
        assertSimpleName "input" tupleValue
        case locatedValue recordPattern of
          GrammarV1RecordPattern name
            [ Located _ firstField
              , Located _ secondField
              ] -> do
                assert
                  (grammarV1QualifiedNameParts (locatedValue name) == ["payload", "Pair"])
                  "record pattern name was not payload.Pair"
                assert (locatedValue (grammarV1FieldPatternName firstField) == "first")
                  "first record field pattern was not first"
                assert (grammarV1FieldPatternValue firstField == Nothing)
                  "first record field unexpectedly had a nested pattern"
                assert (locatedValue (grammarV1FieldPatternName secondField) == "second")
                  "second record field pattern was not second"
                case grammarV1FieldPatternValue secondField of
                  Just (Located _ (GrammarV1TuplePattern [inner, tailPattern])) -> do
                    assertIdentifierPattern "inner" inner
                    assertIdentifierPattern "tail" tailPattern
                  other -> Left ("unexpected second-field nested pattern " <> show other)
          other -> Left ("unexpected record pattern " <> show other)
        assertSimpleName "input" recordValue
        assertSimpleName "left" result
    statements -> Left ("expected two let statements and a return, got " <> show statements)
  where
    source = Text.unlines
      [ "fn destructure(input : Pair) -> U32 satisfies Destructure {"
      , "  let (left, (middle, right)) = input"
      , "  let payload.Pair{first, second = (inner, tail),} = input"
      , "  return left"
      , "}"
      ]

tupleRecordPatternsRejectMalformed :: Either String ()
tupleRecordPatternsRejectMalformed = do
  expectSourceReject "fn bad(input : Pair) satisfies Bad { let (only) = input }"
  expectSourceReject "fn bad(input : Pair) satisfies Bad { let (left, right,) = input }"
  expectSourceReject "fn bad(input : Pair) satisfies Bad { let Pair{} = input }"
  expectSourceReject "fn bad(input : Pair) satisfies Bad { let Pair{left = } = input }"
  expectSourceReject "fn bad(input : Pair) satisfies Bad { let Pair[U32]{left} = input }"
  expectSourceReject "fn bad(input : Pair) satisfies Bad { let payload.Pair = input }"

assertIdentifierPattern :: Text.Text -> Located GrammarV1Pattern -> Either String ()
assertIdentifierPattern expected (Located _ pattern') = case pattern' of
  GrammarV1IdentifierPattern name ->
    assert (locatedValue name == expected)
      ("expected identifier pattern " <> Text.unpack expected)
  other -> Left ("expected identifier pattern, got " <> show other)

expectSourceReject :: Text.Text -> Either String ()
expectSourceReject source =
  case parseGrammarV1StructuralSource "malformed-pattern" source of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

onlyFunction :: GrammarV1SourceFile -> Either String GrammarV1FunctionDecl
onlyFunction sourceFile = case grammarV1TopLevelDecls sourceFile of
  [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1FunctionDeclaration functionDecl -> Right functionDecl
    other -> Left ("expected function declaration, got " <> show other)
  declarations -> Left ("expected one function declaration, got " <> show (length declarations))

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
