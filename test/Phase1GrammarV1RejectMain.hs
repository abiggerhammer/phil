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
    [ testIO "SURF-002 standalone reject fixture preserves exact operand"
        expectStandaloneReject
    , testIO "SURF-003 reject missing operand rejects at syntax"
        (expectFixtureReject "rejected/20-reject-missing-expression.phil")
    , test "SURF-002 nested reject remains structurally parseable"
        nestedRejectPreserved
    , test "SURF-002 reject fallback composes with standalone reject parsing"
        rejectFallbackPreserved
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectStandaloneReject :: IO (Either String ())
expectStandaloneReject = do
  parsed <- parseFixture "accepted/25-standalone-reject.phil"
  pure $ do
    expression <- singleComponentExpression =<< mapLeft show parsed
    case expression of
      GrammarV1RejectExpression operand -> assertSimpleName "x" operand
      other -> Left ("expected reject expression, got " <> show other)

nestedRejectPreserved :: Either String ()
nestedRejectPreserved = do
  expression <- singleComponentExpression =<< mapLeft show
    (parseGrammarV1StructuralSource "nested-reject" source)
  case expression of
    GrammarV1RejectExpression outer -> case locatedValue outer of
      GrammarV1RejectExpression inner -> assertSimpleName "x" inner
      other -> Left ("expected nested reject operand, got " <> show other)
    other -> Left ("expected outer reject expression, got " <> show other)
  where
    source = Text.unlines
      [ "component C(x : U32) {"
      , "  reject reject x"
      , "}"
      ]

rejectFallbackPreserved :: Either String ()
rejectFallbackPreserved = do
  expression <- singleComponentExpression =<< mapLeft show
    (parseGrammarV1StructuralSource "reject-fallback" source)
  case expression of
    GrammarV1FallbackExpression base (Located _ fallback) -> do
      assertSimpleName "x" base
      case fallback of
        GrammarV1RejectFallback value -> assertSimpleName "y" value
        other -> Left ("expected reject fallback, got " <> show other)
    other -> Left ("expected fallback expression, got " <> show other)
  where
    source = "component C(x : U32, y : U32) { x or reject y }"

singleComponentExpression :: GrammarV1SourceFile -> Either String GrammarV1Expression
singleComponentExpression sourceFile =
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
          [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
          statements -> Left ("expected one expression statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one top-level declaration, got " <> show (length declarations))

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
