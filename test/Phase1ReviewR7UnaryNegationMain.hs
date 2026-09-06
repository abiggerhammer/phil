{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.FloatArithmetic
  ( FloatFormat (..)
  , floatDecimalLiteral
  , negativeZero
  , positiveZero
  )
import Phil.Core.NumericConversion
  ( NumericType (..)
  , NumericValue (..)
  )
import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntType (..)
  )
import Phil.Surface.GrammarV1.Lexer
  ( GrammarV1Token (..)
  , lexGrammarV1
  )
import Phil.Surface.GrammarV1.NumericConversion
  ( GrammarV1NumericEvaluationError (..)
  , evaluateGrammarV1NumericExpression
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.RuntimeScalar
  ( grammarV1ContextualFloatLiteral
  , grammarV1ContextualSIntLiteral
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "REVIEW-R07 lexer keeps unary minus separate from numeric literal"
        lexerKeepsMinusSeparate
    , test "REVIEW-R07 negative literal parses as unary expression"
        negativeLiteralIsUnary
    , test "REVIEW-R07 I8 minimum literal checks in full signed context"
        minimumSignedLiteral
    , test "REVIEW-R07 variable negation evaluates exactly"
        variableNegation
    , test "REVIEW-R07 parenthesized subexpression negation evaluates exactly"
        parenthesizedNegation
    , test "REVIEW-R07 repeated negation composes"
        repeatedNegation
    , test "REVIEW-R07 multiplicative unary operand keeps unary precedence"
        multiplicativeNegation
    , test "REVIEW-R07 floating negation preserves signed zero"
        floatingSignedZero
    , test "REVIEW-R07 repeated floating negation restores positive zero"
        repeatedFloatingZero
    , test "REVIEW-R07 unsigned negation rejects rather than wrapping"
        unsignedNegationRejects
    , test "REVIEW-R07 binary subtraction remains binary subtraction"
        binarySubtractionControl
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

lexerKeepsMinusSeparate :: Either String ()
lexerKeepsMinusSeparate = do
  tokens <- mapLeft show (lexGrammarV1 "review-r7-lex" "-128")
  case map locatedValue tokens of
    [GrammarSymbol "-", GrammarDecimalInteger "128"] -> Right ()
    other -> Left ("unary minus was folded into literal token: " <> show other)

negativeLiteralIsUnary :: Either String ()
negativeLiteralIsUnary = do
  expression <- parseExpression "review-r7-literal" "-128"
  case expression of
    GrammarV1NegateExpression (Located _ (GrammarV1IntegerExpression "128")) -> Right ()
    other -> Left ("negative literal did not use unary AST node: " <> show other)

minimumSignedLiteral :: Either String ()
minimumSignedLiteral = do
  expression <- parseExpression "review-r7-i8-min" "-128"
  literal <- mapLeft show
    (grammarV1ContextualSIntLiteral (numericType "I8") expression)
  assert (literal == SIntLiteral (SIntType 8) (-128))
    ("I8 minimum unary literal drifted: " <> show literal)

variableNegation :: Either String ()
variableNegation = do
  expression <- parseExpression "review-r7-variable" "-x"
  let env = Map.singleton (staticReference "x")
        (NumericSIntValue (SIntLiteral (SIntType 8) 5))
  value <- mapLeft show (evaluateGrammarV1NumericExpression env expression)
  assert
    (value == NumericSIntValue (SIntLiteral (SIntType 8) (-5)))
    ("-x did not evaluate to exact signed negation: " <> show value)

parenthesizedNegation :: Either String ()
parenthesizedNegation = do
  expression <- parseExpression "review-r7-parenthesized" "-(x + y)"
  let env = Map.fromList
        [ (staticReference "x", NumericSIntValue (SIntLiteral (SIntType 16) 7))
        , (staticReference "y", NumericSIntValue (SIntLiteral (SIntType 16) 2))
        ]
  value <- mapLeft show (evaluateGrammarV1NumericExpression env expression)
  assert
    (value == NumericSIntValue (SIntLiteral (SIntType 16) (-9)))
    ("-(x+y) did not evaluate exactly: " <> show value)

repeatedNegation :: Either String ()
repeatedNegation = do
  expression <- parseExpression "review-r7-repeat" "--x"
  let env = Map.singleton (staticReference "x")
        (NumericSIntValue (SIntLiteral (SIntType 8) 5))
  value <- mapLeft show (evaluateGrammarV1NumericExpression env expression)
  assert
    (value == NumericSIntValue (SIntLiteral (SIntType 8) 5))
    ("--x did not restore x: " <> show value)

multiplicativeNegation :: Either String ()
multiplicativeNegation = do
  expression <- parseExpression "review-r7-multiply" "x * -y"
  case expression of
    GrammarV1BinaryExpression _ (Located _ GrammarV1Multiply)
      (Located _ (GrammarV1NegateExpression _)) -> Right ()
    other -> Left ("unary precedence under multiplication drifted: " <> show other)
  let env = Map.fromList
        [ (staticReference "x", NumericSIntValue (SIntLiteral (SIntType 8) 3))
        , (staticReference "y", NumericSIntValue (SIntLiteral (SIntType 8) 4))
        ]
  value <- mapLeft show (evaluateGrammarV1NumericExpression env expression)
  assert
    (value == NumericSIntValue (SIntLiteral (SIntType 8) (-12)))
    ("x * -y did not evaluate exactly: " <> show value)

floatingSignedZero :: Either String ()
floatingSignedZero = do
  expression <- parseExpression "review-r7-float-zero" "-0.0"
  literal <- mapLeft show
    (grammarV1ContextualFloatLiteral (numericType "F32") expression)
  assert (literal == negativeZero Float32)
    "unary -0.0 lost floating signed-zero identity"

repeatedFloatingZero :: Either String ()
repeatedFloatingZero = do
  zero <- mapLeft show (floatDecimalLiteral Float32 "0.0")
  expression <- parseExpression "review-r7-float-repeat" "--z"
  value <- mapLeft show
    (evaluateGrammarV1NumericExpression
      (Map.singleton (staticReference "z") (NumericFloatValue zero))
      expression)
  assert (value == NumericFloatValue (positiveZero Float32))
    ("--0.0 did not restore +0.0: " <> show value)

unsignedNegationRejects :: Either String ()
unsignedNegationRejects = do
  expression <- parseExpression "review-r7-uint" "-u"
  case evaluateGrammarV1NumericExpression
      (Map.singleton (staticReference "u") (NumericUIntValue 8 1))
      expression of
    Left (GrammarV1NumericNegationUnsupported (NumericUIntType 8)) -> Right ()
    other -> Left ("unsigned unary negation did not reject exactly: " <> show other)

binarySubtractionControl :: Either String ()
binarySubtractionControl = do
  expression <- parseExpression "review-r7-binary" "5-1"
  case expression of
    GrammarV1BinaryExpression
      (Located _ (GrammarV1IntegerExpression "5"))
      (Located _ GrammarV1Subtract)
      (Located _ (GrammarV1IntegerExpression "1")) -> Right ()
    other -> Left ("binary subtraction was captured as unary syntax: " <> show other)

parseExpression :: Text.Text -> Text.Text -> Either String GrammarV1Expression
parseExpression label source = do
  parsed <- mapLeft show
    (parseGrammarV1StructuralSource label
      ("component C() { " <> source <> "; }"))
  case grammarV1TopLevelDecls parsed of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        case grammarV1BlockStatements
          (locatedValue (grammarV1ComponentBody componentDecl)) of
          [Located _ (GrammarV1ExpressionStatement (Located _ expression))] ->
            Right expression
          statements -> Left
            ("expected one expression statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left
      ("expected one top-level declaration, got " <> show (length declarations))

numericType :: Text.Text -> GrammarV1Type
numericType = GrammarV1UnsignedType

staticReference :: Text.Text -> GrammarV1StaticReference
staticReference name = GrammarV1StaticReference
  { grammarV1StaticReferenceName = GrammarV1QualifiedName [name]
  , grammarV1StaticReferenceArguments = []
  }

assert :: Bool -> String -> Either String ()
assert condition detail = if condition then Right () else Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f result = case result of
  Left err -> Left (f err)
  Right value -> Right value
