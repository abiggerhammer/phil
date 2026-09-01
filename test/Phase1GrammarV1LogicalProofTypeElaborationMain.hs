{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Proposition (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1LogicalProofType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 logical Proof types preserve exact Core meaning"
        logicalProofTypesPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

logicalProofTypesPreserveMeaning :: Either String ()
logicalProofTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-proof-types" source
  actual <- mapM proofType (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "logical proof-type elaboration changed proposition tree or accepted a contextual leaf: " <> show actual
  where
    expected =
      [ Just (TyProof Truth)
      , Just (TyProof (Disjunction (Conjunction (Negation Falsehood) Truth) Falsehood))
      , Nothing
      , Nothing
      ]

proofType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
proofType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1LogicalProofType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type TrivialProof = Proof[true];"
  , "type TreeProof = Proof[not false and true or false];"
  , "type RelationProof = Proof[1 == 0];"
  , "type NotProof = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
