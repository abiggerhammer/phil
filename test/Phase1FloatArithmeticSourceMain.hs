{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.FloatArithmetic
  ( FloatFormat (..)
  , FloatSemanticError (..)
  , FloatValue
  , canonicalNaN
  , floatBits
  , floatCoreType
  , floatDecimalLiteral
  , negativeZero
  , positiveInfinity
  )
import Phil.Core.Protocol.MessageAdmissibility (intrinsicBoundaryMessageType)
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax (Mode (..))
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.FloatArithmetic
  ( GrammarV1FloatArithmeticError (..)
  , evaluateGrammarV1FloatExpression
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BinaryOperator (..)
  , GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1SourceFile (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1TermParam (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.RuntimeScalar
  ( GrammarV1RuntimeScalarError (..)
  , grammarV1ContextualFloatLiteral
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-018 F32/F64 source types retain exact semantic identity" sourceTypeIdentity
    , test "EXEC-018 F32/F64 are unrestricted immutable source scalars" sourceTypeMode
    , test "EXEC-018 F32/F64 are intrinsic Message scalars" sourceMessageCompetence
    , test "EXEC-018 decimal source literals round through Core authority" sourceLiteralRounding
    , test "EXEC-018 negative decimal zero preserves exact sign" sourceNegativeZero
    , test "EXEC-018 parsed +,-,*,/ use strict floating semantics" sourceArithmetic
    , test "EXEC-018 parsed floating division uses IEEE special cases" sourceDivisionSpecialCases
    , test "EXEC-018 parsed nested arithmetic preserves precedence" sourcePrecedence
    , test "EXEC-018 runtime references retain exact float format" sourceReferenceEnvironment
    , test "EXEC-018 F32/F64 reference formats cannot interchange" sourceReferenceFormatMismatch
    , test "EXEC-018 integer-looking literals do not silently become floats" integerLiteralDoesNotDrift
    , test "EXEC-018 % is not silently reinterpreted as floating remainder" floatingRemainderRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

sourceTypeIdentity :: Either String ()
sourceTypeIdentity = do
  types <- parseParameterTypes
    "exec018-types"
    "component C(left : F32, right : F64) { 0.0; }"
  assert (types == [floatType "F32", floatType "F64"])
    ("parser did not preserve F32/F64 carrier identity: " <> show types)
  assert (grammarV1PrimitiveType (floatType "F32") == Just (floatCoreType Float32))
    "F32 did not elaborate to exact Core float identity"
  assert (grammarV1PrimitiveType (floatType "F64") == Just (floatCoreType Float64))
    "F64 did not elaborate to exact Core float identity"

sourceTypeMode :: Either String ()
sourceTypeMode = do
  f32 <- checkedMode (floatType "F32")
  f64 <- checkedMode (floatType "F64")
  assert (checkedBindingMode f32 == Unrestricted)
    "F32 did not receive unrestricted immutable scalar mode"
  assert (checkedBindingMode f64 == Unrestricted)
    "F64 did not receive unrestricted immutable scalar mode"

sourceMessageCompetence :: Either String ()
sourceMessageCompetence = do
  assert (intrinsicBoundaryMessageType (floatCoreType Float32))
    "F32 did not receive intrinsic Message competence"
  assert (intrinsicBoundaryMessageType (floatCoreType Float64))
    "F64 did not receive intrinsic Message competence"

sourceLiteralRounding :: Either String ()
sourceLiteralRounding = do
  expression <- parseExpression "exec018-literal" "component C() { 0.1; }"
  f32 <- mapLeft show (grammarV1ContextualFloatLiteral (floatType "F32") expression)
  f64 <- mapLeft show (grammarV1ContextualFloatLiteral (floatType "F64") expression)
  assert (floatBits f32 == 0x3dcccccd)
    ("F32 0.1 source rounding drifted: " <> show (floatBits f32))
  assert (floatBits f64 == 0x3fb999999999999a)
    ("F64 0.1 source rounding drifted: " <> show (floatBits f64))

sourceNegativeZero :: Either String ()
sourceNegativeZero = do
  expression <- parseExpression "exec018-neg-zero" "component C() { -0.0; }"
  assert (expression == GrammarV1IntegerExpression "-0.0")
    ("negative float literal did not retain exact spelling: " <> show expression)
  value <- mapLeft show (grammarV1ContextualFloatLiteral (floatType "F32") expression)
  assert (value == negativeZero Float32)
    "source -0.0 lost its signed-zero identity"

sourceArithmetic :: Either String ()
sourceArithmetic = do
  addValue <- evaluate "exec018-add" "component C() { 1.5 + 2.25; }"
  subtractValue <- evaluate "exec018-sub" "component C() { 5.0 - 1.5; }"
  multiplyValue <- evaluate "exec018-mul" "component C() { 1.5 * 2.0; }"
  divideValue <- evaluate "exec018-div" "component C() { 7.0 / 2.0; }"
  assert (floatBits addValue == 0x40700000)
    ("1.5+2.25 did not produce F32 3.75: " <> show (floatBits addValue))
  assert (floatBits subtractValue == 0x40600000)
    ("5.0-1.5 did not produce F32 3.5: " <> show (floatBits subtractValue))
  assert (floatBits multiplyValue == 0x40400000)
    ("1.5*2.0 did not produce F32 3.0: " <> show (floatBits multiplyValue))
  assert (floatBits divideValue == 0x40600000)
    ("7.0/2.0 did not produce F32 3.5: " <> show (floatBits divideValue))

sourceDivisionSpecialCases :: Either String ()
sourceDivisionSpecialCases = do
  positive <- evaluate "exec018-inf" "component C() { 1.0 / 0.0; }"
  invalid <- evaluate "exec018-nan" "component C() { 0.0 / 0.0; }"
  assert (positive == positiveInfinity Float32)
    "source floating division by zero did not produce declared +infinity"
  assert (invalid == canonicalNaN Float32)
    "source 0.0/0.0 did not produce canonical NaN"

sourcePrecedence :: Either String ()
sourcePrecedence = do
  value <- evaluate
    "exec018-precedence"
    "component C() { 1.0 + 6.0 / 2.0 * 3.0; }"
  assert (floatBits value == 0x41200000)
    ("parsed floating precedence did not produce F32 10.0: " <> show (floatBits value))

sourceReferenceEnvironment :: Either String ()
sourceReferenceEnvironment = do
  expression <- parseExpression
    "exec018-reference"
    "component C(left : F32, right : F32) { left / right; }"
  left <- literal Float32 "7.0"
  right <- literal Float32 "2.0"
  value <- mapLeft show $
    evaluateGrammarV1FloatExpression
      (floatType "F32")
      (Map.fromList [(staticReference "left", left), (staticReference "right", right)])
      expression
  assert (floatBits value == 0x40600000)
    ("reference-backed F32 division drifted: " <> show (floatBits value))

sourceReferenceFormatMismatch :: Either String ()
sourceReferenceFormatMismatch = do
  expression <- parseExpression
    "exec018-reference-format"
    "component C(left : F32) { left + left; }"
  wrong <- literal Float64 "1.0"
  case evaluateGrammarV1FloatExpression
      (floatType "F32")
      (Map.singleton (staticReference "left") wrong)
      expression of
    Left (GrammarV1FloatOperandFormatMismatch Float32 Float64) -> Right ()
    other -> Left ("F64 value satisfied an F32 source reference: " <> show other)

integerLiteralDoesNotDrift :: Either String ()
integerLiteralDoesNotDrift = do
  expression <- parseExpression "exec018-integer" "component C() { 1; }"
  case grammarV1ContextualFloatLiteral (floatType "F32") expression of
    Left (GrammarV1RuntimeFloatLiteralError (FloatLiteralMalformed "1")) -> Right ()
    other -> Left ("integer literal silently entered F32 semantics: " <> show other)

floatingRemainderRejects :: Either String ()
floatingRemainderRejects = do
  expression <- parseExpression "exec018-rem" "component C() { 5.0 % 2.0; }"
  case evaluateGrammarV1FloatExpression (floatType "F32") Map.empty expression of
    Left (GrammarV1FloatUnsupportedOperator GrammarV1Remainder) -> Right ()
    other -> Left ("floating % acquired undeclared semantics: " <> show other)

checkedMode :: GrammarV1Type -> Either String CheckedTypeMode
checkedMode sourceType =
  case grammarV1CheckedTypeMode emptyStaticContext emptySurfaceState sourceType of
    Just (Right (checked, _)) -> Right checked
    other -> Left ("checked float mode unavailable: " <> show other)

evaluate :: Text -> Text -> Either String FloatValue
evaluate label source = do
  expression <- parseExpression label source
  mapLeft show (evaluateGrammarV1FloatExpression (floatType "F32") Map.empty expression)

literal :: FloatFormat -> Text -> Either String FloatValue
literal format text = mapLeft show (floatDecimalLiteral format text)

parseParameterTypes :: Text -> Text -> Either String [GrammarV1Type]
parseParameterTypes label source = do
  component <- parseComponent label source
  case grammarV1ComponentTermParams component of
    Just params -> Right [locatedValue (grammarV1TermParamType param) | Located _ param <- params]
    Nothing -> Right []

parseExpression :: Text -> Text -> Either String GrammarV1Expression
parseExpression label source = do
  component <- parseComponent label source
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block [Located _ (GrammarV1ExpressionStatement (Located _ expression))] -> Right expression
    block -> Left ("unexpected component body: " <> show block)

parseComponent :: Text -> Text -> Either String GrammarV1ComponentDecl
parseComponent label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration component -> Right component
      other -> Left ("expected component declaration, got " <> show other)
    other -> Left ("expected one top-level declaration, got " <> show other)

floatType :: Text -> GrammarV1Type
floatType = GrammarV1UnsignedType

staticReference :: Text -> GrammarV1StaticReference
staticReference name = GrammarV1StaticReference
  { grammarV1StaticReferenceName = GrammarV1QualifiedName [name]
  , grammarV1StaticReferenceArguments = []
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
