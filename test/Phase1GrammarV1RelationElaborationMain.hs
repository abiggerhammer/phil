{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefTerm (..)
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1RelationProposition)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 relation operators preserve exact Core meaning"
        relationOperatorsPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

relationOperatorsPreserveMeaning :: Either String ()
relationOperatorsPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-relations" source
  operators <- mapM relationOperator (grammarV1TopLevelDecls sourceFile)
  assert (operators == expectedOperators) $
    "parsed relation operator sequence changed: " <> show operators
  let actual = map (\operator -> grammarV1RelationProposition operator leftTerm rightTerm) operators
  assert (actual == expectedPropositions) $
    "relation elaboration changed semantic proposition: " <> show actual
  where
    leftTerm = RefVar (Name "left")
    rightTerm = RefVar (Name "right")
    expectedOperators =
      [ GrammarV1EqualRelation
      , GrammarV1NotEqualRelation
      , GrammarV1LessEqualRelation
      , GrammarV1GreaterEqualRelation
      , GrammarV1LessRelation
      , GrammarV1GreaterRelation
      , GrammarV1InRelation
      , GrammarV1DisjointRelation
      ]
    expectedPropositions =
      [ Equal leftTerm rightTerm
      , NotEqual leftTerm rightTerm
      , LessEqual leftTerm rightTerm
      , LessEqual rightTerm leftTerm
      , LessThan leftTerm rightTerm
      , LessThan rightTerm leftTerm
      , Member leftTerm rightTerm
      , Disjoint leftTerm rightTerm
      ]

relationOperator
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1RelationOperator
relationOperator (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ClaimDeclaration claimDecl ->
      case grammarV1ClaimProposition claimDecl of
        Just (Located _ (GrammarV1RelationProposition _ operator _)) ->
          Right (locatedValue operator)
        other -> Left ("expected relation claim proposition, got " <> show other)
    other -> Left ("expected claim declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "claim Eq(a : U32, b : U32) = a == b;"
  , "claim Ne(a : U32, b : U32) = a != b;"
  , "claim Le(a : U32, b : U32) = a <= b;"
  , "claim Ge(a : U32, b : U32) = a >= b;"
  , "claim Lt(a : U32, b : U32) = a < b;"
  , "claim Gt(a : U32, b : U32) = a > b;"
  , "claim In(a : U32, b : U32) = a in b;"
  , "claim Dj(a : U32, b : U32) = a disjoint b;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
