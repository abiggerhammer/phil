{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.FloatArithmetic
  ( FloatClass (..)
  , FloatFormat (..)
  , canonicalNaN
  , classifyFloat
  , floatBits
  , floatDecimalLiteral
  )
import Phil.Core.NumericConversion
  ( CheckedNumericConversion (..)
  , NumericConversionError (..)
  , NumericConversionPrecision (..)
  , NumericConversionResult (..)
  , NumericType (..)
  , NumericValue (..)
  , checkedConvertNumericValue
  , convertNumericValue
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
  ( GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1SourceFile (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-020 convert syntax is distinct from transport and accept" convertSyntaxIsDistinct
    , test "EXEC-020 UInt widening preserves exact mathematical value" uintWideningExact
    , test "EXEC-020 narrowing succeeds only when the exact value fits" narrowingRangeChecked
    , test "EXEC-020 signed/unsigned boundaries are explicit and checked" signedUnsignedChecked
    , test "EXEC-020 integer-to-float uses declared RNE and reports precision loss" integerToFloatRounded
    , test "EXEC-020 float-to-integer requires finite exact integral value" floatToIntegerExactOnly
    , test "EXEC-020 float width conversion uses semantic float authority" floatWidthConversion
    , test "EXEC-020 checked conversion exposes explicit negative outcome" checkedConversionOutcome
    , test "EXEC-020 mixed-domain arithmetic rejects without explicit convert" implicitMixedArithmeticRejects
    , test "EXEC-020 explicit convert enables domain-appropriate arithmetic" explicitConversionEnablesArithmetic
    , test "EXEC-020 integer division remains integer until explicitly converted" integerDivisionStaysInteger
    , test "EXEC-020 transport and accept are not numeric conversion aliases" transportAcceptAreNotConversions
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

convertSyntaxIsDistinct :: Either String ()
convertSyntaxIsDistinct = do
  converted <- parseReturn "component C { return convert x to F64; }"
  accepted <- parseReturn "component C { return accept x as F64; }"
  transported <- parseReturn "component C { return transport x to F64 using e; }"
  case converted of
    GrammarV1ConvertExpression value target -> do
      assertSimpleName "x" (locatedValue value)
      assert (locatedValue target == GrammarV1UnsignedType "F64")
        ("convert target changed: " <> show (locatedValue target))
    other -> Left ("expected convert expression, got " <> show other)
  case accepted of
    GrammarV1AcceptExpression {} -> Right ()
    other -> Left ("accept was reinterpreted as convert: " <> show other)
  case transported of
    GrammarV1TransportExpression {} -> Right ()
    other -> Left ("transport was reinterpreted as convert: " <> show other)

uintWideningExact :: Either String ()
uintWideningExact = do
  result <- mapLeft show $ convertNumericValue
    (NumericUIntType 16)
    (NumericUIntValue 8 255)
  assert (numericConversionValue result == NumericUIntValue 16 255)
    ("wrong widened value: " <> show result)
  assert (numericConversionPrecision result == NumericConversionExact)
    ("widening was not exact: " <> show result)

narrowingRangeChecked :: Either String ()
narrowingRangeChecked = do
  fitting <- mapLeft show $ convertNumericValue
    (NumericUIntType 8)
    (NumericUIntValue 16 255)
  assert (numericConversionValue fitting == NumericUIntValue 8 255)
    ("fitting narrow changed value: " <> show fitting)
  case convertNumericValue (NumericUIntType 8) (NumericUIntValue 16 256) of
    Left (NumericConversionOutOfRange (NumericUIntType 8) _) -> Right ()
    other -> Left ("out-of-range narrowing did not reject exactly: " <> show other)

signedUnsignedChecked :: Either String ()
signedUnsignedChecked = do
  widened <- mapLeft show $ convertNumericValue
    (NumericSIntType (SIntType 16))
    (NumericUIntValue 8 255)
  assert
    (numericConversionValue widened == NumericSIntValue (SIntLiteral (SIntType 16) 255))
    ("UInt-to-wider-I conversion changed value: " <> show widened)
  case convertNumericValue
      (NumericUIntType 8)
      (NumericSIntValue (SIntLiteral (SIntType 8) (-1))) of
    Left (NumericConversionOutOfRange (NumericUIntType 8) _) -> Right ()
    other -> Left ("negative signed value silently became UInt: " <> show other)
  case convertNumericValue
      (NumericSIntType (SIntType 8))
      (NumericUIntValue 8 255) of
    Left (NumericConversionOutOfRange (NumericSIntType (SIntType 8)) _) -> Right ()
    other -> Left ("255 silently became I8: " <> show other)

integerToFloatRounded :: Either String ()
integerToFloatRounded = do
  result <- mapLeft show $ convertNumericValue
    (NumericFloatType Float32)
    (NumericUIntValue 64 16777217)
  assert (numericConversionPrecision result == NumericConversionRounded)
    ("precision loss was not reported: " <> show result)
  case numericConversionValue result of
    NumericFloatValue value ->
      assert (floatBits value == 0x4b800000)
        ("RNE result was not exact F32 16777216: " <> show (floatBits value))
    other -> Left ("integer-to-float returned non-float: " <> show other)

floatToIntegerExactOnly :: Either String ()
floatToIntegerExactOnly = do
  integral <- mapLeft show $ floatDecimalLiteral Float64 "42.0"
  converted <- mapLeft show $ convertNumericValue
    (NumericSIntType (SIntType 8))
    (NumericFloatValue integral)
  assert
    (numericConversionValue converted == NumericSIntValue (SIntLiteral (SIntType 8) 42))
    ("exact integral float conversion changed value: " <> show converted)
  fractional <- mapLeft show $ floatDecimalLiteral Float64 "1.5"
  case convertNumericValue (NumericUIntType 8) (NumericFloatValue fractional) of
    Left (NumericConversionFractional (NumericUIntType 8) _) -> Right ()
    other -> Left ("fractional float silently rounded to integer: " <> show other)
  case convertNumericValue
      (NumericUIntType 8)
      (NumericFloatValue (canonicalNaN Float64)) of
    Left (NumericConversionNonFinite (NumericUIntType 8) (FloatNaN _)) -> Right ()
    other -> Left ("NaN silently became integer: " <> show other)

floatWidthConversion :: Either String ()
floatWidthConversion = do
  source <- mapLeft show $ floatDecimalLiteral Float32 "0.1"
  result <- mapLeft show $ convertNumericValue
    (NumericFloatType Float64)
    (NumericFloatValue source)
  assert (numericConversionPrecision result == NumericConversionExact)
    ("F32-to-F64 exact value was not preserved: " <> show result)
  case numericConversionValue result of
    NumericFloatValue widened ->
      case (classifyFloat source, classifyFloat widened) of
        (FloatFinite before, FloatFinite after) ->
          assert (before == after) "F32-to-F64 changed the exact represented rational"
        classes -> Left ("unexpected finite conversion classes: " <> show classes)
    other -> Left ("float width conversion returned non-float: " <> show other)

checkedConversionOutcome :: Either String ()
checkedConversionOutcome =
  case checkedConvertNumericValue
      (NumericUIntType 8)
      (NumericUIntValue 16 300) of
    CheckedNumericConversionFailed
      (NumericConversionOutOfRange (NumericUIntType 8) _) -> Right ()
    other -> Left ("checked narrowing did not expose exact failure: " <> show other)

implicitMixedArithmeticRejects :: Either String ()
implicitMixedArithmeticRejects = do
  expression <- parseReturn "component C { return n + f; }"
  half <- mapLeft show $ floatDecimalLiteral Float64 "0.5"
  let environment = Map.fromList
        [ (simpleReference "n", NumericUIntValue 32 2)
        , (simpleReference "f", NumericFloatValue half)
        ]
  case evaluateGrammarV1NumericExpression environment expression of
    Left (GrammarV1NumericMixedDomainRequiresConversion
      (NumericUIntType 32) (NumericFloatType Float64)) -> Right ()
    other -> Left ("mixed arithmetic was not rejected at domain boundary: " <> show other)

explicitConversionEnablesArithmetic :: Either String ()
explicitConversionEnablesArithmetic = do
  expression <- parseReturn "component C { return (convert n to F64) + f; }"
  half <- mapLeft show $ floatDecimalLiteral Float64 "0.5"
  let environment = Map.fromList
        [ (simpleReference "n", NumericUIntValue 32 2)
        , (simpleReference "f", NumericFloatValue half)
        ]
  result <- mapLeft show $ evaluateGrammarV1NumericExpression environment expression
  case result of
    NumericFloatValue value -> case classifyFloat value of
      FloatFinite rational -> assert (rational == 5 / 2)
        ("converted float arithmetic produced wrong value: " <> show rational)
      other -> Left ("converted float arithmetic produced non-finite value: " <> show other)
    other -> Left ("converted arithmetic returned wrong domain: " <> show other)

integerDivisionStaysInteger :: Either String ()
integerDivisionStaysInteger = do
  integerExpression <- parseReturn "component C { return n / d; }"
  floatExpression <- parseReturn "component C { return (convert n to F64) / f; }"
  two <- mapLeft show $ floatDecimalLiteral Float64 "2.0"
  let integerEnvironment = Map.fromList
        [ (simpleReference "n", NumericUIntValue 32 7)
        , (simpleReference "d", NumericUIntValue 32 2)
        ]
      floatEnvironment = Map.fromList
        [ (simpleReference "n", NumericUIntValue 32 7)
        , (simpleReference "f", NumericFloatValue two)
        ]
  integerResult <- mapLeft show $
    evaluateGrammarV1NumericExpression integerEnvironment integerExpression
  assert (integerResult == NumericUIntValue 32 3)
    ("I/U division stopped being integer quotient: " <> show integerResult)
  floatResult <- mapLeft show $
    evaluateGrammarV1NumericExpression floatEnvironment floatExpression
  case floatResult of
    NumericFloatValue value -> case classifyFloat value of
      FloatFinite rational -> assert (rational == 7 / 2)
        ("explicit floating quotient was wrong: " <> show rational)
      other -> Left ("explicit floating quotient was non-finite: " <> show other)
    other -> Left ("explicit floating quotient stayed integer: " <> show other)

transportAcceptAreNotConversions :: Either String ()
transportAcceptAreNotConversions = do
  accepted <- parseReturn "component C { return accept x as U16; }"
  transported <- parseReturn "component C { return transport x to U16 using e; }"
  let environment = Map.singleton (simpleReference "x") (NumericUIntValue 8 7)
  case evaluateGrammarV1NumericExpression environment accepted of
    Left (GrammarV1NumericUnsupportedExpression GrammarV1AcceptExpression {}) -> Right ()
    other -> Left ("accept entered numeric conversion semantics: " <> show other)
  case evaluateGrammarV1NumericExpression environment transported of
    Left (GrammarV1NumericUnsupportedExpression GrammarV1TransportExpression {}) -> Right ()
    other -> Left ("transport entered numeric conversion semantics: " <> show other)

parseReturn :: String -> Either String GrammarV1Expression
parseReturn source = do
  parsed <- mapLeft show $ parseGrammarV1StructuralSource "exec-020.phil" (fromString source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case grammarV1Declaration top of
      GrammarV1ComponentDeclaration component ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
          [Located _ (GrammarV1ReturnStatement expression)] -> Right (locatedValue expression)
          statements -> Left ("expected one return statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show declarations)

simpleReference :: String -> GrammarV1StaticReference
simpleReference name = GrammarV1StaticReference
  { grammarV1StaticReferenceName = GrammarV1QualifiedName [fromString name]
  , grammarV1StaticReferenceArguments = []
  }

assertSimpleName :: String -> GrammarV1Expression -> Either String ()
assertSimpleName expected expression = case expression of
  GrammarV1NameExpression reference [] ->
    assert (reference == simpleReference expected)
      ("expected name " <> expected <> ", got " <> show reference)
  other -> Left ("expected simple name, got " <> show other)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

fromString :: String -> Text.Text
fromString = Text.pack

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
