{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( StaticContext
  , declareOpaqueClaim
  , declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
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
import Phil.Surface.GrammarV1.CheckedRefinementType
  ( grammarV1CheckedRefinementType
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
    , test "SURF-008 binder-scoped Grammar-v1 refinement types preserve lexical predicate meaning and focused coercion"
        boundRefinementTypesPreserveMeaning
    , test "SURF-008 checked Grammar-v1 refinement predicates delegate once to Core focusing"
        checkedRefinementTypesUseCoreFocusing
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
        , Just
            (TyRefined
              (Name "v")
              (TyUInt 8)
              (LessThan (RefNat 0) (RefToNat (RefVar (Name "v")))))
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "binder-scoped refinement elaboration changed lexical meaning or accepted an unresolved predicate/base: " <> show actual

checkedRefinementTypesUseCoreFocusing :: Either String ()
checkedRefinementTypesUseCoreFocusing = do
  staticContext <- checkedClaimContext
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-checked-refinement-types" checkedSource
  sourceTypes <- mapM typeAliasTarget (grammarV1TopLevelDecls sourceFile)
  case sourceTypes of
    [ positive
      , coercing
      , flagged
      , relation
      , unknown
      , arity
      , sortMismatch
      , reverseCoercion
      , specialized
      , unresolved
      , nonPrimitive
      , notRefinement
      ] -> do
        let v = RefVar (Name "v")
            flag = RefVar (Name "flag")
            checked = grammarV1CheckedRefinementType staticContext emptySurfaceState
        expectCheckedTy
          (TyRefined
            (Name "v")
            (TyUInt 8)
            (LessThan (RefNat 0) (RefToNat v)))
          [ExpandedTransparentClaim "Positive"]
          (checked positive)
        expectCheckedTy
          (TyRefined
            (Name "v")
            (TyUInt 8)
            (Atom "NeedsNat" [RefToNat v]))
          [InsertedUIntToNat v]
          (checked coercing)
        expectCheckedTy
          (TyRefined
            (Name "flag")
            TyBool
            (Atom "Flagged" [flag]))
          []
          (checked flagged)
        expectCheckedTy
          (TyRefined
            (Name "v")
            (TyUInt 8)
            (LessThan (RefNat 0) (RefToNat v)))
          []
          (checked relation)
        expectCoreError
          (UnknownClaim "Missing")
          (checked unknown)
        expectCoreError
          (ClaimArityMismatch "Positive" 1 2)
          (checked arity)
        expectCoreError
          (ClaimArgumentSortMismatch "Flagged" 0 SortBool (SortUInt 8))
          (checked sortMismatch)
        expectCoreError
          (ClaimArgumentSortMismatch "NeedsUInt" 0 (SortUInt 8) SortNat)
          (checked reverseCoercion)
        expectStructuralNothing (checked specialized)
        expectStructuralNothing (checked unresolved)
        expectStructuralNothing (checked nonPrimitive)
        expectStructuralNothing (checked notRefinement)
        shadowState <- bind "v" Unrestricted (TyUInt 8) emptySurfaceState
        expectStructuralNothing
          (grammarV1CheckedRefinementType staticContext shadowState positive)
    other -> Left
      ("expected twelve checked refinement source types, got " <> show (length other))

checkedClaimContext :: Either String StaticContext
checkedClaimContext = do
  context1 <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext
  context2 <- mapLeft show $
    declareOpaqueClaim "NeedsNat" [(Name "n", SortNat)] context1
  context3 <- mapLeft show $
    declareOpaqueClaim "Flagged" [(Name "flag", SortBool)] context2
  mapLeft show $
    declareOpaqueClaim "NeedsUInt" [(Name "x", SortUInt 8)] context3

expectCheckedTy
  :: Ty
  -> [FocusStep]
  -> Maybe (Either FocusingError (Ty, [FocusStep]))
  -> Either String ()
expectCheckedTy expected requiredSteps result =
  case result of
    Just (Right (actual, steps)) -> do
      assert (actual == expected) $
        "checked refinement changed canonical type meaning: " <> show actual
      mapM_
        (\step -> assert (step `elem` steps) $
          "checked refinement omitted required Core focusing step " <> show step
            <> " from " <> show steps)
        requiredSteps
    other -> Left ("expected checked refinement success, got " <> show other)

expectCoreError
  :: FocusingError
  -> Maybe (Either FocusingError (Ty, [FocusStep]))
  -> Either String ()
expectCoreError expected result =
  case result of
    Just (Left actual) ->
      assert (actual == expected) $
        "checked refinement changed Core rejection: expected " <> show expected
          <> ", got " <> show actual
    other -> Left ("expected checked refinement Core rejection, got " <> show other)

expectStructuralNothing
  :: Maybe (Either FocusingError (Ty, [FocusStep]))
  -> Either String ()
expectStructuralNothing result =
  case result of
    Nothing -> Right ()
    other -> Left
      ("expected refinement source non-competence, got " <> show other)

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

typeAliasTarget
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1Type
typeAliasTarget (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (locatedValue (grammarV1TypeAliasTarget aliasDecl))
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

checkedSource :: Text.Text
checkedSource = Text.unlines
  [ "type PositiveRefinement = {v : U8 | Positive(v)};"
  , "type CoercingRefinement = {v : U8 | NeedsNat(v)};"
  , "type FlagRefinement = {flag : Bool | Flagged(flag)};"
  , "type RelationRefinement = {v : U8 | v > 0};"
  , "type UnknownRefinement = {v : U8 | Missing(v)};"
  , "type ArityRefinement = {v : U8 | Positive(v, v)};"
  , "type SortRefinement = {v : U8 | Flagged(v)};"
  , "type ReverseCoercion = {v : U8 | NeedsUInt(1)};"
  , "type Specialized = {v : U8 | Positive[U8](v)};"
  , "type Unresolved = {v : U8 | Positive(missing)};"
  , "type NonPrimitive = {v : Frame[Hello] | true};"
  , "type NotRefinement = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
