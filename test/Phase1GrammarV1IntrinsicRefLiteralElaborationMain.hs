{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (RefTerm (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1IntrinsicRefLiteral)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 intrinsic scalar literals elaborate exactly"
        intrinsicLiteralsElaborateExactly
    , test "SURF-008 names and unit remain outside the context-free literal bridge"
        contextualFormsFailClosed
    , test "SURF-008 malformed constructed integer literal fails closed"
        malformedIntegerFailsClosed
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicLiteralsElaborateExactly :: Either String ()
intrinsicLiteralsElaborateExactly = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-ref-literals" source
  case grammarV1TopLevelDecls sourceFile of
    [natTop, _, _] -> do
      (natLeft, natRight) <- relationOperands natTop
      assert
        ( grammarV1IntrinsicRefLiteral natLeft == Just (RefNat 7)
          && grammarV1IntrinsicRefLiteral natRight == Just (RefNat 0)
        )
        "natural-number literal elaboration changed exact values"
      assert
        ( grammarV1IntrinsicRefLiteral (GrammarV1BoolExpression True) == Just (RefBool True)
          && grammarV1IntrinsicRefLiteral (GrammarV1BoolExpression False) == Just (RefBool False)
        )
        "Boolean literal elaboration changed exact values"
    declarations -> Left ("expected three claim declarations, got " <> show (length declarations))

contextualFormsFailClosed :: Either String ()
contextualFormsFailClosed = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-ref-contextual" source
  case grammarV1TopLevelDecls sourceFile of
    [_, nameTop, unitTop] -> do
      (nameLeft, nameRight) <- relationOperands nameTop
      assert
        ( grammarV1IntrinsicRefLiteral nameLeft == Nothing
          && grammarV1IntrinsicRefLiteral nameRight == Just (RefNat 1)
        )
        "bare name was guessed into a context-free reference-term category"
      (unitLeft, unitRight) <- relationOperands unitTop
      assert
        ( grammarV1IntrinsicRefLiteral unitLeft == Nothing
          && grammarV1IntrinsicRefLiteral unitRight == Nothing
        )
        "unit expression unexpectedly acquired a Core reference-term encoding"
    declarations -> Left ("expected three claim declarations, got " <> show (length declarations))

malformedIntegerFailsClosed :: Either String ()
malformedIntegerFailsClosed =
  assert
    (grammarV1IntrinsicRefLiteral (GrammarV1IntegerExpression "12x") == Nothing)
    "malformed constructed integer text was partially consumed"

source :: Text.Text
source = Text.unlines
  [ "claim NatLit() = 7 == 0;"
  , "claim NameLit(x : U32) = x == 1;"
  , "claim UnitLit() = unit == unit;"
  ]

relationOperands
  :: Located GrammarV1TopLevelDecl
  -> Either String (GrammarV1Expression, GrammarV1Expression)
relationOperands (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ClaimDeclaration claimDecl ->
      case grammarV1ClaimProposition claimDecl of
        Just (Located _ (GrammarV1RelationProposition left _ right)) ->
          Right (locatedValue left, locatedValue right)
        other -> Left ("expected relation proposition, got " <> show other)
    other -> Left ("expected claim declaration, got " <> show other)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
