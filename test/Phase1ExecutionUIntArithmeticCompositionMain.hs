{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , emptyCheckState
  )
import Phil.Core.Process
  ( ProcessFlow
  , continueFlow
  , flowPaths
  , joinBranches
  , pathState
  )
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , RefSort (..)
  , RefTerm (..)
  )
import Phil.Core.UIntArithmetic
  ( PlainUIntArithmeticDecision (..)
  , PlainUIntArithmeticSite (..)
  , UIntArithmeticError (..)
  , UIntArithmeticOperator (..)
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
import Phil.Surface.GrammarV1.UIntArithmetic
  ( GrammarV1PlainUIntArithmeticError (..)
  , checkGrammarV1PlainUIntArithmetic
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-008 parsed closed UInt arithmetic uses exact Core semantics"
        parsedClosedArithmetic
    , test "EXEC-008 parsed overflow cannot acquire wrapping target behavior"
        parsedOverflowRejects
    , test "EXEC-008 branch-local arithmetic obligation survives RES-011 reconvergence"
        branchLocalArithmeticObligationSurvives
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

parsedClosedArithmetic :: Either String ()
parsedClosedArithmetic = do
  expression <- parseComponentExpression
    "exec-008-closed"
    "component Arithmetic(x : U8) { 10 + 20; }"
  (decision, nextState) <- mapLeft show
    (checkGrammarV1PlainUIntArithmetic
      emptyCheckState
      (GrammarV1UnsignedType "U8")
      Map.empty
      expression
      (RefUInt 8 30)
      (site "exec008.grammar.closed"))
  assert
    (decision == PlainUIntArithmeticEstablished (ScalarUIntLiteral 8 30))
    "parsed closed addition did not establish its exact mathematical result"
  assert
    (Map.null (residualObligations nextState))
    "closed exact arithmetic invented a residual proof obligation"

parsedOverflowRejects :: Either String ()
parsedOverflowRejects = do
  expression <- parseComponentExpression
    "exec-008-overflow"
    "component Arithmetic(x : U8) { 255 + 1; }"
  case checkGrammarV1PlainUIntArithmetic
      emptyCheckState
      (GrammarV1UnsignedType "U8")
      Map.empty
      expression
      (RefUInt 8 0)
      (site "exec008.grammar.overflow") of
    Left
      (GrammarV1PlainUIntCoreError
        (UIntArithmeticKnownResultOutOfRange UIntAdd 8 255 1 256)) -> Right ()
    other -> Left
      ("parsed U8 overflow did not reject before target behavior selection: " <> show other)

branchLocalArithmeticObligationSurvives :: Either String ()
branchLocalArithmeticObligationSurvives = do
  expression <- parseComponentExpression
    "exec-008-branch"
    "component Arithmetic(left : U8, right : U8) { left * right; }"
  let leftReference = staticReference "left"
      rightReference = staticReference "right"
      environment = Map.fromList
        [ (leftReference, RefOpaque (SortUInt 8) "exec008.left")
        , (rightReference, RefOpaque (SortUInt 8) "exec008.right")
        ]
      result = RefOpaque (SortUInt 8) "exec008.result"
      arithmeticSite = site "exec008.branch.pending"
  (decision, arithmeticState) <- mapLeft show
    (checkGrammarV1PlainUIntArithmetic
      emptyCheckState
      (GrammarV1UnsignedType "U8")
      environment
      expression
      result
      arithmeticSite)
  obligation <- case decision of
    PlainUIntArithmeticRequiresProof actual -> Right actual
    other -> Left
      ("symbolic Grammar-v1 multiplication did not produce an ordinary obligation: " <> show other)
  assert
    (obligationId obligation == ObligationId "exec008.branch.pending")
    "arithmetic obligation lost its exact branch-local identity"
  assert
    (Map.lookup (obligationId obligation) (residualObligations arithmeticState) == Just obligation)
    "Grammar-v1 arithmetic did not emit its unresolved Core obligation into CheckState"

  joined <- mapLeft show
    (joinBranches
      [ continueFlow arithmeticState
      , continueFlow emptyCheckState
      ])
  assertExactlyOnePathCarries obligation joined

parseComponentExpression :: Text -> Text -> Either String GrammarV1Expression
parseComponentExpression label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration component ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
          [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
          statements -> Left ("expected one expression statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left
      ("expected one top-level declaration, got " <> show (length declarations))

staticReference :: Text -> GrammarV1StaticReference
staticReference name = GrammarV1StaticReference
  { grammarV1StaticReferenceName = GrammarV1QualifiedName [name]
  , grammarV1StaticReferenceArguments = []
  }

site :: Text -> PlainUIntArithmeticSite
site identifier = PlainUIntArithmeticSite
  { plainUIntArithmeticObligationId = ObligationId identifier
  , plainUIntArithmeticOrigin = "EXEC-008"
  , plainUIntArithmeticScope = "Grammar-v1 execution composition"
  , plainUIntArithmeticRequiredPoint = "before arithmetic result use or branch reconvergence"
  }

assertExactlyOnePathCarries :: Obligation -> ProcessFlow -> Either String ()
assertExactlyOnePathCarries obligation flow =
  case
    [ actual
    | path <- flowPaths flow
    , let state = pathState path
    , Just actual <- [Map.lookup (obligationId obligation) (residualObligations state)]
    ] of
    [actual] -> assert
      (actual == obligation)
      "RES-011 reconvergence changed the exact arithmetic obligation"
    [] -> Left "branch-local arithmetic obligation disappeared at reconvergence"
    obligations -> Left
      ("branch-local arithmetic obligation duplicated across "
        <> show (length obligations)
        <> " continuing paths")

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
