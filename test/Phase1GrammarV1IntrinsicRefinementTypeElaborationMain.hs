{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , insertBindingMeta
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundRefinementType
  ( grammarV1BoundRefinementType
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
    , test "SURF-008 binder-scoped Grammar-v1 refinement types preserve lexical predicate meaning"
        boundRefinementTypesPreserveMeaning
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicRefinementTypesPreserveMeaning :: Either String ()
intrinsicRefinementTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-refinement-types" intrinsicSource
  actual <- mapM intrinsicRefinementType (grammarV1TopLevelDecls sourceFile)
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

boundRefinementTypesPreserveMeaning :: Either String ()
boundRefinementTypesPreserveMeaning = do
  state <- bind "limit" Unrestricted (TyUInt 8) emptySurfaceState
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-refinement-types" boundSource
  actual <- mapM (boundRefinementType state) (grammarV1TopLevelDecls sourceFile)
  let expected =
        [ Just
            (TyRefined
              (Name "flag")
              TyBool
              (Equal (RefVar (Name "flag")) (RefBool True)))
        , Just
            (TyRefined
              (Name "v")
              (TyUInt 8)
              (LessEqual (RefVar (Name "v")) (RefVar (Name "limit"))))
        , Just
            (TyRefined
              (Name "flag")
              TyBool
              (Atom "Ready" [RefVar (Name "flag")]))
        , Just (TyRefined (Name "v") (TyUInt 8) Truth)
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "binder-scoped refinement elaboration changed lexical meaning or accepted an unresolved predicate/base: " <> show actual

intrinsicRefinementType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
intrinsicRefinementType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right
        (grammarV1IntrinsicRefinementType
          (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

boundRefinementType
  :: SurfaceState
  -> Located GrammarV1TopLevelDecl
  -> Either String (Maybe Ty)
boundRefinementType state (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right
        (grammarV1BoundRefinementType
          state
          (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta mode ty PlainShape) state

intrinsicSource :: Text.Text
intrinsicSource = Text.unlines
  [ "type Always = {v : U8 | true};"
  , "type LiteralTree = {flag : Bool | 1 == 1 and not false};"
  , "type ClaimTree = {word : U32 | Ready(1, true)};"
  , "type UsesBinder = {v : U8 | v > 0};"
  , "type NonPrimitiveBase = {v : Frame[Hello] | true};"
  , "type SpecializedClaim = {v : U8 | Ready[U8](1)};"
  , "type NotRefinement = Bool;"
  ]

boundSource :: Text.Text
boundSource = Text.unlines
  [ "type BinderBoolRelation = {flag : Bool | flag == true};"
  , "type OuterRelation = {v : U8 | v <= limit};"
  , "type BinderClaim = {flag : Bool | Ready(flag)};"
  , "type Intrinsic = {v : U8 | true};"
  , "type NatLiteralNeedsCoercion = {v : U8 | v > 0};"
  , "type Unknown = {v : U8 | v == missing};"
  , "type Arithmetic = {v : U8 | v + 1 == v};"
  , "type Specialized = {v : U8 | Ready[U8](v)};"
  , "type NonPrimitiveBase = {v : Frame[Hello] | true};"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
