{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.FloatArithmetic (FloatFormat (..), floatDecimalLiteral)
import Phil.Core.IntegerShift
  ( IntegerShiftError (..)
  )
import Phil.Core.NumericConversion
  ( NumericType (..)
  , NumericValue (..)
  )
import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntType (..)
  )
import Phil.Surface.GrammarV1.NumericConversion
  ( GrammarV1NumericEvaluationError (..)
  , evaluateGrammarV1NumericExpression
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BinaryOperator (..)
  , GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1ShiftOperator (..)
  , GrammarV1SourceFile (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1TopLevelDecl (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-021 shift precedence is lower than additive" shiftPrecedence
    , test "EXEC-021 shift chains are left-associative" shiftAssociativity
    , test "EXEC-021 UInt left shift is exact multiplication" uintLeftExact
    , test "EXEC-021 left shift never discards high bits" leftOverflowRejects
    , test "EXEC-021 shift counts are exact and never masked" countBoundaries
    , test "EXEC-021 UInt right shift is logical floor division" uintRightLogical
    , test "EXEC-021 signed right shift is arithmetic floor" signedRightArithmetic
    , test "EXEC-021 signed left shift is representability checked" signedLeftChecked
    , test "EXEC-021 signed logical shift requires unsigned conversion" explicitUnsignedSelectsLogical
    , test "EXEC-021 floating operands cannot enter integer shift semantics" floatShiftRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

shiftPrecedence :: Either String ()
shiftPrecedence = do
  expression <- parseReturn "component C { return a + b << k; }"
  case expression of
    GrammarV1ShiftExpression left operator _ -> do
      assert (locatedValue operator == GrammarV1ShiftLeft) "wrong shift operator"
      case locatedValue left of
        GrammarV1BinaryExpression _ binaryOperator _ ->
          assert (locatedValue binaryOperator == GrammarV1Add)
            "additive expression did not bind before shift"
        other -> Left ("expected additive left operand, got " <> show other)
    other -> Left ("expected shift expression, got " <> show other)

shiftAssociativity :: Either String ()
shiftAssociativity = do
  expression <- parseReturn "component C { return a << b >> c; }"
  case expression of
    GrammarV1ShiftExpression left outerOperator _ -> do
      assert (locatedValue outerOperator == GrammarV1ShiftRight) "wrong outer shift"
      case locatedValue left of
        GrammarV1ShiftExpression _ innerOperator _ ->
          assert (locatedValue innerOperator == GrammarV1ShiftLeft)
            "shift chain was not left-associative"
        other -> Left ("expected nested left shift, got " <> show other)
    other -> Left ("expected shift chain, got " <> show other)

uintLeftExact :: Either String ()
uintLeftExact = do
  result <- evaluate "x << k"
    [ ("x", NumericUIntValue 8 3), ("k", NumericUIntValue 8 2) ]
  assert (result == NumericUIntValue 8 12) ("wrong UInt left shift: " <> show result)

leftOverflowRejects :: Either String ()
leftOverflowRejects = do
  expression <- parseReturn "component C { return x << k; }"
  case evaluateGrammarV1NumericExpression (environment
      [("x", NumericUIntValue 8 128), ("k", NumericUIntValue 8 1)]) expression of
    Left (GrammarV1NumericShiftError (IntegerShiftUIntLeftResultOutOfRange 8 256)) -> Right ()
    other -> Left ("high bits were silently discarded: " <> show other)

countBoundaries :: Either String ()
countBoundaries = do
  zero <- evaluate "x >> k"
    [("x", NumericUIntValue 8 5), ("k", NumericUIntValue 8 0)]
  assert (zero == NumericUIntValue 8 5) "shift by zero changed value"
  maxCount <- evaluate "x >> k"
    [("x", NumericUIntValue 8 255), ("k", NumericUIntValue 8 7)]
  assert (maxCount == NumericUIntValue 8 1) "w-1 shift produced wrong result"
  expression <- parseReturn "component C { return x >> k; }"
  case evaluateGrammarV1NumericExpression (environment
      [("x", NumericUIntValue 8 255), ("k", NumericUIntValue 8 8)]) expression of
    Left (GrammarV1NumericShiftError (IntegerShiftCountOutOfRange 8 8)) -> Right ()
    other -> Left ("count w was masked or accepted: " <> show other)
  case evaluateGrammarV1NumericExpression (environment
      [("x", NumericUIntValue 8 255),
       ("k", NumericSIntValue (SIntLiteral (SIntType 8) (-1)))]) expression of
    Left (GrammarV1NumericShiftError (IntegerShiftCountOutOfRange 8 (-1))) -> Right ()
    other -> Left ("negative count was accepted: " <> show other)

uintRightLogical :: Either String ()
uintRightLogical = do
  result <- evaluate "x >> k"
    [("x", NumericUIntValue 8 255), ("k", NumericUIntValue 8 1)]
  assert (result == NumericUIntValue 8 127) ("wrong logical right shift: " <> show result)

signedRightArithmetic :: Either String ()
signedRightArithmetic = do
  shifted <- evaluate "x >> k"
    [ ("x", NumericSIntValue (SIntLiteral (SIntType 8) (-3)))
    , ("k", NumericUIntValue 8 1)
    ]
  assert (shifted == NumericSIntValue (SIntLiteral (SIntType 8) (-2)))
    ("signed >> did not floor: " <> show shifted)
  divided <- evaluate "x / d"
    [ ("x", NumericSIntValue (SIntLiteral (SIntType 8) (-3)))
    , ("d", NumericSIntValue (SIntLiteral (SIntType 8) 2))
    ]
  assert (divided == NumericSIntValue (SIntLiteral (SIntType 8) (-1)))
    "signed >> accidentally inherited truncating division semantics"

signedLeftChecked :: Either String ()
signedLeftChecked = do
  exact <- evaluate "x << k"
    [ ("x", NumericSIntValue (SIntLiteral (SIntType 8) (-3)))
    , ("k", NumericUIntValue 8 2)
    ]
  assert (exact == NumericSIntValue (SIntLiteral (SIntType 8) (-12)))
    ("wrong signed left shift: " <> show exact)
  expression <- parseReturn "component C { return x << k; }"
  case evaluateGrammarV1NumericExpression (environment
      [ ("x", NumericSIntValue (SIntLiteral (SIntType 8) 64))
      , ("k", NumericUIntValue 8 1)
      ]) expression of
    Left (GrammarV1NumericShiftError
      (IntegerShiftSIntLeftResultOutOfRange (SIntType 8) 128)) -> Right ()
    other -> Left ("signed left overflow did not reject: " <> show other)

explicitUnsignedSelectsLogical :: Either String ()
explicitUnsignedSelectsLogical = do
  direct <- evaluate "x >> k"
    [ ("x", NumericSIntValue (SIntLiteral (SIntType 8) 100))
    , ("k", NumericUIntValue 8 2)
    ]
  converted <- evaluate "(convert x to U8) >> k"
    [ ("x", NumericSIntValue (SIntLiteral (SIntType 8) 100))
    , ("k", NumericUIntValue 8 2)
    ]
  assert (direct == NumericSIntValue (SIntLiteral (SIntType 8) 25))
    "direct signed shift changed domain"
  assert (converted == NumericUIntValue 8 25)
    "explicit conversion did not select unsigned logical domain"

floatShiftRejects :: Either String ()
floatShiftRejects = do
  floatValue <- mapLeft show $ floatDecimalLiteral Float32 "1.0"
  expression <- parseReturn "component C { return f >> k; }"
  case evaluateGrammarV1NumericExpression (environment
      [("f", NumericFloatValue floatValue), ("k", NumericUIntValue 8 1)]) expression of
    Left (GrammarV1NumericShiftOperandIntegerRequired (NumericFloatType Float32)) -> Right ()
    other -> Left ("floating operand entered shift semantics: " <> show other)

evaluate :: String -> [(String, NumericValue)] -> Either String NumericValue
evaluate source bindings = do
  expression <- parseReturn ("component C { return " <> source <> "; }")
  mapLeft show $ evaluateGrammarV1NumericExpression (environment bindings) expression

environment :: [(String, NumericValue)] -> Map.Map GrammarV1StaticReference NumericValue
environment = Map.fromList . map (\(name, value) -> (simpleReference name, value))

parseReturn :: String -> Either String GrammarV1Expression
parseReturn source = do
  parsed <- mapLeft show $ parseGrammarV1StructuralSource "exec-021.phil" (Text.pack source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1ComponentDeclaration component ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
          [Located _ (GrammarV1ReturnStatement expression)] -> Right (locatedValue expression)
          statements -> Left ("expected one return statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show declarations)

simpleReference :: String -> GrammarV1StaticReference
simpleReference name = GrammarV1StaticReference
  { grammarV1StaticReferenceName = GrammarV1QualifiedName [Text.pack name]
  , grammarV1StaticReferenceArguments = []
  }

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
