{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.IntrinsicProofType
  ( grammarV1IntrinsicProofType
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic Proof composition preserves exact Core meaning"
        intrinsicProofTypesPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicProofTypesPreserveMeaning :: Either String ()
intrinsicProofTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-proof-composition" source
  actual <- mapM proofType (grammarV1TopLevelDecls sourceFile)
  assert (actual == expected) $
    "intrinsic Proof composition changed a verified leaf/tree or accepted contextual specialization: " <> show actual
  where
    expected =
      [ Just (TyProof (GreaterThanCanonical 7 3))
      , Just (TyProof (Conjunction (Atom "Ready" [RefNat 1]) (Negation Falsehood)))
      , Just (TyProof (Disjunction (Equal (RefNat 1) (RefNat 1)) (Atom "Flag" [RefBool True])))
      , Nothing
      , Nothing
      , Nothing
      ]

    GreaterThanCanonical left right = LessThan (RefNat right) (RefNat left)

proofType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
proofType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1IntrinsicProofType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type RelationProof = Proof[7 > 3];"
  , "type ClaimProof = Proof[Ready(1) and not false];"
  , "type MixedProof = Proof[1 == 1 or Flag(true)];"
  , "type ContextProof = Proof[x == 0];"
  , "type SpecializedProof = Proof[Ready[U32](1)];"
  , "type NotProof = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
