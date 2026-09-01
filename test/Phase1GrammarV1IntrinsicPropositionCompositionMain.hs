{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Proposition (..), RefTerm (..))
import Phil.Surface.GrammarV1.IntrinsicProposition
  ( grammarV1IntrinsicProposition
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic proposition fragments compose exactly and fail closed"
        intrinsicPropositionsComposeExactly
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicPropositionsComposeExactly :: Either String ()
intrinsicPropositionsComposeExactly = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-propositions" source
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let actual = map grammarV1IntrinsicProposition propositions
      expected =
        [ Just (Conjunction (Negation Falsehood) Truth)
        , Just (Conjunction Truth (LessThan (RefNat 3) (RefNat 7)))
        , Just (Disjunction (Atom "Ready" [RefNat 1, RefBool True]) Falsehood)
        , Just
            ( Disjunction
                (Conjunction (Negation Falsehood) (LessThan (RefNat 3) (RefNat 7)))
                (Atom "Ready" [RefNat 1, RefBool True])
            )
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "intrinsic proposition composition changed a verified leaf/tree or accepted a contextual leaf: " <> show actual

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
  [ "claim TruthTree = not false and true;"
  , "claim RelationTree = true and 7 > 3;"
  , "claim ClaimTree = Ready(1, true) or false;"
  , "claim MixedTree = not false and 7 > 3 or Ready(1, true);"
  , "claim Contextual(x : U32) = true and x == 1;"
  , "claim Specialized = true and Ready[U32](1);"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
