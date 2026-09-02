{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.IntrinsicRefinementType
  ( grammarV1IntrinsicRefinementType
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic Grammar-v1 refinement types preserve exact Core structure and fail closed"
        intrinsicRefinementTypesPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicRefinementTypesPreserveMeaning :: Either String ()
intrinsicRefinementTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-refinement-types" source
  actual <- mapM refinementType (grammarV1TopLevelDecls sourceFile)
  let expected =
        [ Just (TyRefined (Name "v") (TyUInt 8) Truth)
        , Just
            (TyRefined
              (Name "flag")
              TyBool
              (Conjunction
                (Equal (RefNat 1) (RefNat 1))
                (Negation Falsehood)))
        , Just
            (TyRefined
              (Name "word")
              (TyUInt 32)
              (Atom "Ready" [RefNat 1, RefBool True]))
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "intrinsic refinement elaboration changed binder/base/predicate identity or accepted contextual structure: " <> show actual

refinementType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
refinementType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right
        (grammarV1IntrinsicRefinementType
          (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type Always = {v : U8 | true};"
  , "type LiteralTree = {flag : Bool | 1 == 1 and not false};"
  , "type ClaimTree = {word : U32 | Ready(1, true)};"
  , "type UsesBinder = {v : U8 | v > 0};"
  , "type NonPrimitiveBase = {v : Frame[Hello] | true};"
  , "type SpecializedClaim = {v : U8 | Ready[U8](1)};"
  , "type NotRefinement = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
