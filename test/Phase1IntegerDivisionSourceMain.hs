{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , emptyCheckState
  )
import Phil.Core.IntegerDivision
  ( CheckedDivisionResult (..)
  , PlainIntegerDivisionSite (..)
  , PlainSIntDivisionDecision (..)
  , PlainUIntDivisionDecision (..)
  , UIntDivisionError (..)
  , checkedIntegerDivideByZeroFailure
  , checkedSignedDivisionOverflowFailure
  )
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntTerm (..)
  , SIntType (..)
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , RefSort (..)
  , RefTerm (..)
  )
import Phil.Surface.GrammarV1.IntegerDivision
  ( GrammarV1PlainUIntDivisionError (..)
  , checkGrammarV1CheckedSIntDivision
  , checkGrammarV1CheckedUIntDivision
  , checkGrammarV1PlainSIntDivision
  , checkGrammarV1PlainUIntDivision
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
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.SIntArithmetic
  ( GrammarV1PlainSIntArithmeticError (..)
  , checkGrammarV1PlainSIntArithmetic
  )
import Phil.Surface.GrammarV1.UIntArithmetic
  ( GrammarV1PlainUIntArithmeticError (..)
  , checkGrammarV1PlainUIntArithmetic
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-017 / and % retain exact multiplicative operator identity"
        parserOperatorIdentity
    , test "EXEC-017 / and % remain left-associative at multiplicative precedence"
        parserPrecedence
    , test "EXEC-017 Grammar-v1 UInt quotient/remainder compose exactly"
        uintComposition
    , test "EXEC-017 Grammar-v1 signed quotient truncates toward zero"
        signedQuotientComposition
    , test "EXEC-017 Grammar-v1 signed remainder keeps dividend sign"
        signedRemainderComposition
    , test "EXEC-017 plain parsed zero divisor rejects before target behavior"
        parsedZeroDivisorRejects
    , test "EXEC-017 checked parsed zero divisor selects exact typed-negative outcome"
        checkedParsedZeroDivisor
    , test "EXEC-017 parsed minInt/-1 checked quotient selects overflow outcome"
        checkedParsedMinimumOverflow
    , test "EXEC-017 parsed minInt%-1 remains exact zero"
        parsedMinimumRemainder
    , test "EXEC-017 symbolic parsed division enters ordinary residual obligations"
        symbolicDivisionObligation
    , test "EXEC-017 EXEC-008 UInt bridge cannot reinterpret / as old arithmetic"
        uintArithmeticBridgeRejectsDivision
    , test "EXEC-017 EXEC-016 signed bridge cannot reinterpret % as old arithmetic"
        sintArithmeticBridgeRejectsRemainder
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

parserOperatorIdentity :: Either String ()
parserOperatorIdentity = do
  divide <- parseExpression "exec017-div-op" "component C() { 8 / 3; }"
  remainder <- parseExpression "exec017-rem-op" "component C() { 8 % 3; }"
  assertBinaryOperator GrammarV1Divide divide
  assertBinaryOperator GrammarV1Remainder remainder

parserPrecedence :: Either String ()
parserPrecedence = do
  expression <- parseExpression
    "exec017-precedence"
    "component C() { 1 + 8 / 3 % 2 * 4; }"
  case expression of
    GrammarV1BinaryExpression
      (Located _ (GrammarV1IntegerExpression "1"))
      (Located _ GrammarV1Add)
      (Located _ multiplicative) -> case multiplicative of
        GrammarV1BinaryExpression
          (Located _ remainder)
          (Located _ GrammarV1Multiply)
          (Located _ (GrammarV1IntegerExpression "4")) -> case remainder of
            GrammarV1BinaryExpression
              (Located _ divide)
              (Located _ GrammarV1Remainder)
              (Located _ (GrammarV1IntegerExpression "2")) -> case divide of
                GrammarV1BinaryExpression
                  (Located _ (GrammarV1IntegerExpression "8"))
                  (Located _ GrammarV1Divide)
                  (Located _ (GrammarV1IntegerExpression "3")) -> Right ()
                other -> Left ("leftmost division identity/precedence changed: " <> show other)
            other -> Left ("remainder associativity changed: " <> show other)
        other -> Left ("multiplication associativity changed: " <> show other)
    other -> Left ("additive precedence over /%/* changed: " <> show other)

uintComposition :: Either String ()
uintComposition = do
  divide <- parseExpression "exec017-uint-div" "component C() { 7 / 3; }"
  remainder <- parseExpression "exec017-uint-rem" "component C() { 7 % 3; }"
  (quotDecision, quotientState) <- mapLeft show $
    checkGrammarV1PlainUIntDivision
      emptyCheckState
      (GrammarV1UnsignedType "U8")
      Map.empty
      divide
      (RefUInt 8 2)
      (site "exec017.source.uint.quot")
  (remDecision, remainderState) <- mapLeft show $
    checkGrammarV1PlainUIntDivision
      emptyCheckState
      (GrammarV1UnsignedType "U8")
      Map.empty
      remainder
      (RefUInt 8 1)
      (site "exec017.source.uint.rem")
  assert
    (quotDecision == PlainUIntDivisionEstablished (ScalarUIntLiteral 8 2))
    ("unexpected parsed UInt quotient: " <> show quotDecision)
  assert
    (remDecision == PlainUIntDivisionEstablished (ScalarUIntLiteral 8 1))
    ("unexpected parsed UInt remainder: " <> show remDecision)
  assert (Map.null (residualObligations quotientState))
    "closed UInt quotient invented an obligation"
  assert (Map.null (residualObligations remainderState))
    "closed UInt remainder invented an obligation"

signedQuotientComposition :: Either String ()
signedQuotientComposition = do
  expression <- parseExpression "exec017-sint-div" "component C() { -7 / 3; }"
  let ty = SIntType 8
  (decision, nextState) <- mapLeft show $
    checkGrammarV1PlainSIntDivision
      emptyCheckState
      (signedType "I8")
      Map.empty
      expression
      (knownS 8 (-2))
      (site "exec017.source.sint.quot")
  assert
    (decision == PlainSIntDivisionEstablished (SIntLiteral ty (-2)))
    ("signed quotient was not truncation toward zero: " <> show decision)
  assert (Map.null (residualObligations nextState))
    "closed signed quotient invented an obligation"

signedRemainderComposition :: Either String ()
signedRemainderComposition = do
  expression <- parseExpression "exec017-sint-rem" "component C() { -7 % 3; }"
  let ty = SIntType 8
  (decision, _) <- mapLeft show $
    checkGrammarV1PlainSIntDivision
      emptyCheckState
      (signedType "I8")
      Map.empty
      expression
      (knownS 8 (-1))
      (site "exec017.source.sint.rem")
  assert
    (decision == PlainSIntDivisionEstablished (SIntLiteral ty (-1)))
    ("signed remainder did not retain dividend sign: " <> show decision)

parsedZeroDivisorRejects :: Either String ()
parsedZeroDivisorRejects = do
  expression <- parseExpression "exec017-zero" "component C() { 9 / 0; }"
  case checkGrammarV1PlainUIntDivision
      emptyCheckState
      (GrammarV1UnsignedType "U8")
      Map.empty
      expression
      (RefUInt 8 0)
      (site "exec017.source.zero") of
    Left (GrammarV1PlainUIntDivisionCoreError (UIntDivisionKnownZeroDivisor 8 9)) -> Right ()
    other -> Left ("parsed zero divisor did not reject semantically: " <> show other)

checkedParsedZeroDivisor :: Either String ()
checkedParsedZeroDivisor = do
  expression <- parseExpression "exec017-checked-zero" "component C() { 9 % 0; }"
  decision <- mapLeft show $
    checkGrammarV1CheckedUIntDivision
      (GrammarV1UnsignedType "U8")
      expression
      (ScalarUIntLiteral 8 9)
      (ScalarUIntLiteral 8 0)
  assert
    (decision == CheckedDivisionNegative checkedIntegerDivideByZeroFailure)
    ("parsed checked zero divisor changed failure: " <> show decision)

checkedParsedMinimumOverflow :: Either String ()
checkedParsedMinimumOverflow = do
  expression <- parseExpression "exec017-min-overflow" "component C() { -128 / -1; }"
  let ty = SIntType 8
  decision <- mapLeft show $
    checkGrammarV1CheckedSIntDivision
      (signedType "I8")
      expression
      (SIntLiteral ty (-128))
      (SIntLiteral ty (-1))
  assert
    (decision == CheckedDivisionNegative checkedSignedDivisionOverflowFailure)
    ("parsed minInt/-1 changed checked overflow outcome: " <> show decision)

parsedMinimumRemainder :: Either String ()
parsedMinimumRemainder = do
  expression <- parseExpression "exec017-min-rem" "component C() { -128 % -1; }"
  let ty = SIntType 8
  decision <- mapLeft show $
    checkGrammarV1CheckedSIntDivision
      (signedType "I8")
      expression
      (SIntLiteral ty (-128))
      (SIntLiteral ty (-1))
  case decision of
    CheckedDivisionSucceeded literal _ ->
      assert (literal == SIntLiteral ty 0)
        ("parsed minInt%-1 changed exact zero: " <> show literal)
    other -> Left ("parsed minInt%-1 unexpectedly failed: " <> show other)

symbolicDivisionObligation :: Either String ()
symbolicDivisionObligation = do
  expression <- parseExpression "exec017-symbolic" "component C(left : U16, right : U16) { left / right; }"
  let leftReference = staticReference "left"
      rightReference = staticReference "right"
      environment = Map.fromList
        [ (leftReference, RefOpaque (SortUInt 16) "exec017.source.left")
        , (rightReference, RefOpaque (SortUInt 16) "exec017.source.right")
        ]
      result = RefOpaque (SortUInt 16) "exec017.source.result"
      obligationId' = ObligationId "exec017.source.symbolic"
  (decision, nextState) <- mapLeft show $
    checkGrammarV1PlainUIntDivision
      emptyCheckState
      (GrammarV1UnsignedType "U16")
      environment
      expression
      result
      (site "exec017.source.symbolic")
  obligation <- case decision of
    PlainUIntDivisionRequiresProof value -> Right value
    other -> Left ("symbolic parsed division did not retain obligation: " <> show other)
  assert (obligationId obligation == obligationId')
    "symbolic parsed division changed obligation identity"
  assert
    (Map.lookup obligationId' (residualObligations nextState) == Just obligation)
    "symbolic parsed division obligation did not enter CheckState"

uintArithmeticBridgeRejectsDivision :: Either String ()
uintArithmeticBridgeRejectsDivision = do
  expression <- parseExpression "exec017-old-uint" "component C() { 8 / 2; }"
  case checkGrammarV1PlainUIntArithmetic
      emptyCheckState
      (GrammarV1UnsignedType "U8")
      Map.empty
      expression
      (RefUInt 8 4)
      (error "EXEC-008 site must not be demanded after operator rejection") of
    Left (GrammarV1PlainUIntOperatorNotPlainArithmetic GrammarV1Divide) -> Right ()
    other -> Left ("EXEC-008 bridge reinterpreted division: " <> show other)

sintArithmeticBridgeRejectsRemainder :: Either String ()
sintArithmeticBridgeRejectsRemainder = do
  expression <- parseExpression "exec017-old-sint" "component C() { -7 % 3; }"
  case checkGrammarV1PlainSIntArithmetic
      emptyCheckState
      (signedType "I8")
      Map.empty
      expression
      (knownS 8 (-1))
      (error "EXEC-016 site must not be demanded after operator rejection") of
    Left (GrammarV1PlainSIntOperatorNotPlainArithmetic GrammarV1Remainder) -> Right ()
    other -> Left ("EXEC-016 bridge reinterpreted remainder: " <> show other)

assertBinaryOperator :: GrammarV1BinaryOperator -> GrammarV1Expression -> Either String ()
assertBinaryOperator expected expression = case expression of
  GrammarV1BinaryExpression _ (Located _ actual) _ ->
    assert (actual == expected)
      ("expected operator " <> show expected <> ", got " <> show actual)
  other -> Left ("expected binary expression, got " <> show other)

parseExpression :: Text -> Text -> Either String GrammarV1Expression
parseExpression label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration component ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
          [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
          statements -> Left ("expected one expression statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

knownS :: Int -> Integer -> SIntTerm
knownS width value =
  let ty = SIntType width
  in SIntKnown (SIntLiteral ty value)

signedType :: Text -> GrammarV1Type
signedType = GrammarV1UnsignedType

staticReference :: Text -> GrammarV1StaticReference
staticReference name = GrammarV1StaticReference
  { grammarV1StaticReferenceName = GrammarV1QualifiedName [name]
  , grammarV1StaticReferenceArguments = []
  }

site :: Text -> PlainIntegerDivisionSite
site identifier = PlainIntegerDivisionSite
  { plainIntegerDivisionObligationId = ObligationId identifier
  , plainIntegerDivisionOrigin = "EXEC-017"
  , plainIntegerDivisionScope = "Grammar-v1 fixed-width integer division"
  , plainIntegerDivisionRequiredPoint = "before quotient/remainder result use"
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
