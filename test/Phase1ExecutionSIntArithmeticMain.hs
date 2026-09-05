{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , emptyCheckState
  )
import Phil.Core.SIntArithmetic
  ( PlainSIntArithmeticDecision (..)
  , PlainSIntArithmeticSite (..)
  , SIntArithmeticError (..)
  , SIntArithmeticOperator (..)
  , plainSIntArithmeticProposition
  )
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
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
  , grammarV1ContextualSIntLiteral
  )
import Phil.Surface.GrammarV1.SIntArithmetic
  ( GrammarV1PlainSIntArithmeticError (..)
  , checkGrammarV1PlainSIntArithmetic
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-016 I8/I32/I64 source types retain signed semantic identity"
        signedTypeWidthsParse
    , test "EXEC-016 negative I8 boundary literal parses and elaborates exactly"
        negativeBoundaryLiteral
    , test "EXEC-016 positive I8 boundary literal elaborates exactly"
        positiveBoundaryLiteral
    , test "EXEC-016 signed literals outside I8 range reject"
        signedLiteralRangeRejects
    , test "EXEC-016 parsed signed addition uses exact mathematical semantics"
        signedAddition
    , test "EXEC-016 signed overflow cannot acquire wrapping or target UB semantics"
        signedOverflowRejects
    , test "EXEC-016 signed underflow cannot acquire wrapping or target UB semantics"
        signedUnderflowRejects
    , test "EXEC-016 symbolic signed arithmetic retains an ordinary proof obligation"
        symbolicSignedArithmetic
    , test "EXEC-016 signedness is semantic and U8 cannot satisfy an I8 context"
        signednessMismatchRejects
    , test "EXEC-016 binary subtraction remains distinct from unary negative literal"
        binarySubtractionStillParses
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

signedTypeWidthsParse :: Either String ()
signedTypeWidthsParse = do
  component <- parseComponent
    "exec-016-types"
    "component Signed(a : I8, b : I32, c : I64) { a + a; }"
  let types =
        [ locatedValue (grammarV1TermParamType (locatedValue parameter))
        | parameter <- maybe [] id (grammarV1ComponentTermParams component)
        ]
  assert
    (map grammarV1PrimitiveType types == [Just (TySInt 8), Just (TySInt 32), Just (TySInt 64)])
    ("I<w> parser carrier lost signed width identity: " <> show types)

negativeBoundaryLiteral :: Either String ()
negativeBoundaryLiteral = do
  expression <- parseComponentExpression
    "exec-016-negative-boundary"
    "component Signed(x : I8) { -128; }"
  assert
    (expression == GrammarV1IntegerExpression "-128")
    ("negative literal sign was not preserved by source parsing: " <> show expression)
  literal <- mapLeft show
    (grammarV1ContextualSIntLiteral (signedType "I8") expression)
  assert
    (literal == ScalarSIntLiteral 8 (-128))
    "I8 minimum literal did not elaborate exactly"

positiveBoundaryLiteral :: Either String ()
positiveBoundaryLiteral = do
  expression <- parseComponentExpression
    "exec-016-positive-boundary"
    "component Signed(x : I8) { 127; }"
  literal <- mapLeft show
    (grammarV1ContextualSIntLiteral (signedType "I8") expression)
  assert
    (literal == ScalarSIntLiteral 8 127)
    "I8 maximum literal did not elaborate exactly"

signedLiteralRangeRejects :: Either String ()
signedLiteralRangeRejects = do
  negative <- parseComponentExpression
    "exec-016-negative-out-of-range"
    "component Signed(x : I8) { -129; }"
  positive <- parseComponentExpression
    "exec-016-positive-out-of-range"
    "component Signed(x : I8) { 128; }"
  case grammarV1ContextualSIntLiteral (signedType "I8") negative of
    Left (GrammarV1RuntimeSIntLiteralOutOfRange 8 (-129)) -> Right ()
    other -> Left ("I8 -129 did not reject at exact signed range boundary: " <> show other)
  case grammarV1ContextualSIntLiteral (signedType "I8") positive of
    Left (GrammarV1RuntimeSIntLiteralOutOfRange 8 128) -> Right ()
    other -> Left ("I8 128 did not reject at exact signed range boundary: " <> show other)

signedAddition :: Either String ()
signedAddition = do
  expression <- parseComponentExpression
    "exec-016-add"
    "component Signed(x : I8) { -40 + 10; }"
  (decision, nextState) <- mapLeft show
    (checkGrammarV1PlainSIntArithmetic
      emptyCheckState
      (signedType "I8")
      Map.empty
      expression
      (RefSInt 8 (-30))
      (site "exec016.signed.add"))
  assert
    (decision == PlainSIntArithmeticEstablished (ScalarSIntLiteral 8 (-30)))
    "signed addition did not establish exact mathematical result"
  assert (Map.null (residualObligations nextState))
    "closed signed arithmetic invented a residual obligation"

signedOverflowRejects :: Either String ()
signedOverflowRejects = do
  expression <- parseComponentExpression
    "exec-016-overflow"
    "component Signed(x : I8) { 127 + 1; }"
  case checkGrammarV1PlainSIntArithmetic
      emptyCheckState
      (signedType "I8")
      Map.empty
      expression
      (RefSInt 8 (-128))
      (site "exec016.signed.overflow") of
    Left
      (GrammarV1PlainSIntCoreError
        (SIntArithmeticKnownResultOutOfRange SIntAdd 8 127 1 128)) -> Right ()
    other -> Left
      ("I8 overflow did not reject before wrap/trap/UB selection: " <> show other)

signedUnderflowRejects :: Either String ()
signedUnderflowRejects = do
  expression <- parseComponentExpression
    "exec-016-underflow"
    "component Signed(x : I8) { -128 - 1; }"
  case checkGrammarV1PlainSIntArithmetic
      emptyCheckState
      (signedType "I8")
      Map.empty
      expression
      (RefSInt 8 127)
      (site "exec016.signed.underflow") of
    Left
      (GrammarV1PlainSIntCoreError
        (SIntArithmeticKnownResultOutOfRange SIntSubtract 8 (-128) 1 (-129))) -> Right ()
    other -> Left
      ("I8 underflow did not reject before wrap/trap/UB selection: " <> show other)

symbolicSignedArithmetic :: Either String ()
symbolicSignedArithmetic = do
  expression <- parseComponentExpression
    "exec-016-symbolic"
    "component Signed(left : I32, right : I32) { left * right; }"
  let leftReference = staticReference "left"
      rightReference = staticReference "right"
      environment = Map.fromList
        [ (leftReference, RefOpaque (SortSInt 32) "exec016.left")
        , (rightReference, RefOpaque (SortSInt 32) "exec016.right")
        ]
      result = RefOpaque (SortSInt 32) "exec016.result"
  (decision, nextState) <- mapLeft show
    (checkGrammarV1PlainSIntArithmetic
      emptyCheckState
      (signedType "I32")
      environment
      expression
      result
      (site "exec016.symbolic"))
  obligation <- case decision of
    PlainSIntArithmeticRequiresProof actual -> Right actual
    other -> Left ("symbolic signed multiply did not emit obligation: " <> show other)
  assert
    (Map.lookup (obligationId obligation) (residualObligations nextState) == Just obligation)
    "signed arithmetic obligation did not enter ordinary CheckState"
  assert
    (obligationProposition obligation
      == plainSIntArithmeticProposition
          SIntMultiply 32
          (environment Map.! leftReference)
          (environment Map.! rightReference)
          result)
    "signed arithmetic obligation changed exact mathematical proposition"

signednessMismatchRejects :: Either String ()
signednessMismatchRejects = do
  expression <- parseComponentExpression
    "exec-016-signedness"
    "component Signed(x : I8) { 1; }"
  case grammarV1ContextualSIntLiteral (GrammarV1UnsignedType "U8") expression of
    Left (GrammarV1RuntimeSIntContextRequired (GrammarV1UnsignedType "U8")) -> Right ()
    other -> Left ("U8 was accepted as an I8 context: " <> show other)

binarySubtractionStillParses :: Either String ()
binarySubtractionStillParses = do
  expression <- parseComponentExpression
    "exec-016-binary-minus"
    "component Signed(x : I8) { 5-1; }"
  case expression of
    GrammarV1BinaryExpression
      (Located _ (GrammarV1IntegerExpression "5"))
      _
      (Located _ (GrammarV1IntegerExpression "1")) -> Right ()
    other -> Left ("binary subtraction was swallowed by signed literal lexing: " <> show other)

signedType :: Text -> GrammarV1Type
signedType = GrammarV1UnsignedType

parseComponent :: Text -> Text -> Either String GrammarV1ComponentDecl
parseComponent label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration component -> Right component
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left
      ("expected one top-level declaration, got " <> show (length declarations))

parseComponentExpression :: Text -> Text -> Either String GrammarV1Expression
parseComponentExpression label source = do
  component <- parseComponent label source
  case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
    [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
    statements -> Left ("expected one expression statement, got " <> show statements)

staticReference :: Text -> GrammarV1StaticReference
staticReference name = GrammarV1StaticReference
  { grammarV1StaticReferenceName = GrammarV1QualifiedName [name]
  , grammarV1StaticReferenceArguments = []
  }

site :: Text -> PlainSIntArithmeticSite
site identifier = PlainSIntArithmeticSite
  { plainSIntArithmeticObligationId = ObligationId identifier
  , plainSIntArithmeticOrigin = "EXEC-016"
  , plainSIntArithmeticScope = "Grammar-v1 signed integer execution"
  , plainSIntArithmeticRequiredPoint = "before signed arithmetic result use"
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
