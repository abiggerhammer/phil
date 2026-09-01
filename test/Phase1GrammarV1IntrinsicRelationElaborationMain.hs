{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Proposition (..), RefTerm (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1IntrinsicRelationProposition)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic relation leaves preserve exact Core meaning"
        intrinsicRelationsPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicRelationsPreserveMeaning :: Either String ()
intrinsicRelationsPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-relations" source
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let actual = map grammarV1IntrinsicRelationProposition propositions
      expected =
        [ Just (Equal (RefNat 7) (RefNat 0))
        , Just (LessThan (RefNat 4) (RefNat 9))
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "intrinsic relation elaboration changed meaning or accepted contextual operands: " <> show actual

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
  [ "claim EqLeaf = 7 == 0;"
  , "claim GreaterLeaf = 9 > 4;"
  , "claim NameLeaf(x : U32) = x == 1;"
  , "claim CompoundLeaf = 1 + 2 == 3;"
  , "claim TruthLeaf = true;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
