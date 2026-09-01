{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Proposition (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1LogicalProposition)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 logical proposition structure preserves exact Core meaning"
        logicalPropositionsPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

logicalPropositionsPreserveMeaning :: Either String ()
logicalPropositionsPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-logical" source
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let actual = map grammarV1LogicalProposition propositions
      expected =
        [ Just Truth
        , Just Falsehood
        , Just (Negation Truth)
        , Just (Conjunction Truth Falsehood)
        , Just (Disjunction Truth Falsehood)
        , Just (Disjunction (Conjunction (Negation Falsehood) Truth) Falsehood)
        , Nothing
        ]
  assert (actual == expected) $
    "logical elaboration changed connective tree or accepted an atomic leaf: " <> show actual

claimProposition
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1Proposition
claimProposition (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ClaimDeclaration claimDecl ->
      case grammarV1ClaimProposition claimDecl of
        Just proposition -> Right (locatedValue proposition)
        Nothing -> Left "claim had no proposition"
    other -> Left ("expected claim declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "claim TruthClaim = true;"
  , "claim FalseClaim = false;"
  , "claim NotClaim = not true;"
  , "claim AndClaim = true and false;"
  , "claim OrClaim = true or false;"
  , "claim TreeClaim = not false and true or false;"
  , "claim RelationClaim(a : U32, b : U32) = a == b;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
