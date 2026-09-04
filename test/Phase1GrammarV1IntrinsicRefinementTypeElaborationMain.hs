{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , StaticContext
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
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1BindLocal
  , grammarV1RootLexicalScope
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
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticRefinementType
  ( GrammarV1CheckedSemanticRefinementType (..)
  , GrammarV1SemanticRefinementTypeError (..)
  , grammarV1CheckedSemanticRefinementType
  )
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
    , test "SURF-009 semantic refinement binders use generated Core identity"
        semanticRefinementUsesGeneratedIdentity
    , test "SURF-009 semantic refinement binders are alpha-stable"
        semanticRefinementAlphaStable
    , test "SURF-009 sibling refinements advance one declaration-wide ordinal stream"
        semanticRefinementOrdinalsAdvance
    , test "SURF-009 refinement shadowing follows lexical identity, not SurfaceState spelling"
        semanticRefinementShadowingUsesLexicalScope
    , test "SURF-009 semantic refinement focusing failures remain explicit"
        semanticRefinementFocusingFailurePreserved
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

semanticRefinementUsesGeneratedIdentity :: Either String ()
semanticRefinementUsesGeneratedIdentity = do
  staticContext <- checkedClaimContext
  sourceType <- oneTypeAliasTarget
    "type Semantic = {v : U8 | NeedsNat(v)};"
  let declarationKey = DeclarationKey "decl.SemanticRefinement"
      rootScope = grammarV1RootLexicalScope declarationKey
  (checked, _) <- expectSemanticSuccess
    ( grammarV1CheckedSemanticRefinementType
        staticContext
        rootScope
        emptySurfaceState
        sourceType
    )
  let binder = checkedSemanticRefinementBinder checked
      semanticName = grammarV1ResolvedBinderCoreName binder
      expectedType = TyRefined
        semanticName
        (TyUInt 8)
        (Atom "NeedsNat" [RefToNat (RefVar semanticName)])
  assert (grammarV1ResolvedBinderKind binder == GrammarV1RefinementBinder)
    "semantic refinement used the wrong binder family"
  assert (semanticName /= Name "v")
    "semantic refinement reused source spelling as Core identity"
  assert (checkedSemanticRefinementType checked == expectedType)
    ("semantic refinement did not rewrite predicate identity: "
      <> show (checkedSemanticRefinementType checked))
  reference <- exactlyOne
    "semantic refinement predicate reference"
    (checkedSemanticRefinementReferences checked)
  assert
    ( grammarV1ResolvedBinderKey
        (grammarV1CheckedLexicalReferenceBinder reference)
        == grammarV1ResolvedBinderKey binder
    )
    "semantic refinement predicate evidence did not point at its exact binder"
  assert
    (InsertedUIntToNat (RefVar semanticName)
      `elem` checkedSemanticRefinementFocusSteps checked)
    "semantic refinement lost Core UInt-to-Nat focusing evidence"

semanticRefinementAlphaStable :: Either String ()
semanticRefinementAlphaStable = do
  staticContext <- checkedClaimContext
  original <- oneTypeAliasTarget
    "type Original = {v : U8 | NeedsNat(v)};"
  renamed <- oneTypeAliasTarget
    "type Renamed = {count : U8 | NeedsNat(count)};"
  let declarationKey = DeclarationKey "decl.SemanticRefinementAlpha"
  (originalChecked, _) <- expectSemanticSuccess
    ( grammarV1CheckedSemanticRefinementType
        staticContext
        (grammarV1RootLexicalScope declarationKey)
        emptySurfaceState
        original
    )
  (renamedChecked, _) <- expectSemanticSuccess
    ( grammarV1CheckedSemanticRefinementType
        staticContext
        (grammarV1RootLexicalScope declarationKey)
        emptySurfaceState
        renamed
    )
  let originalBinder = checkedSemanticRefinementBinder originalChecked
      renamedBinder = checkedSemanticRefinementBinder renamedChecked
  assert
    (grammarV1ResolvedBinderKey originalBinder == grammarV1ResolvedBinderKey renamedBinder)
    "alpha-renaming changed semantic refinement BinderKey"
  assert
    (grammarV1ResolvedBinderCoreName originalBinder == grammarV1ResolvedBinderCoreName renamedBinder)
    "alpha-renaming changed semantic refinement Core name"
  assert
    (checkedSemanticRefinementType originalChecked
      == checkedSemanticRefinementType renamedChecked)
    "alpha-renaming changed semantic refinement Core type"
  assert
    (grammarV1ResolvedBinderDisplayName originalBinder /= grammarV1ResolvedBinderDisplayName renamedBinder)
    "alpha-renaming test did not actually change source spelling"

semanticRefinementOrdinalsAdvance :: Either String ()
semanticRefinementOrdinalsAdvance = do
  staticContext <- checkedClaimContext
  firstType <- oneTypeAliasTarget
    "type First = {v : U8 | NeedsNat(v)};"
  secondType <- oneTypeAliasTarget
    "type Second = {v : U8 | NeedsNat(v)};"
  let rootScope = grammarV1RootLexicalScope
        (DeclarationKey "decl.SemanticRefinementSequence")
  (firstChecked, afterFirst) <- expectSemanticSuccess
    ( grammarV1CheckedSemanticRefinementType
        staticContext rootScope emptySurfaceState firstType
    )
  (secondChecked, _) <- expectSemanticSuccess
    ( grammarV1CheckedSemanticRefinementType
        staticContext afterFirst emptySurfaceState secondType
    )
  let firstBinder = checkedSemanticRefinementBinder firstChecked
      secondBinder = checkedSemanticRefinementBinder secondChecked
  assert
    ( map (grammarV1BinderOrdinal . grammarV1ResolvedBinderKey)
        [firstBinder, secondBinder]
        == [0, 1]
    )
    "sibling refinements restarted or skipped the declaration-wide ordinal stream"
  assert
    (grammarV1ResolvedBinderCoreName firstBinder
      /= grammarV1ResolvedBinderCoreName secondBinder)
    "sibling refinements reused semantic Core identity"

semanticRefinementShadowingUsesLexicalScope :: Either String ()
semanticRefinementShadowingUsesLexicalScope = do
  staticContext <- checkedClaimContext
  sourceType <- oneTypeAliasTarget
    "type Shadow = {v : U8 | NeedsNat(v)};"
  let declarationKey = DeclarationKey "decl.SemanticRefinementShadow"
      rootScope = grammarV1RootLexicalScope declarationKey
  spellingState <- bind "v" Unrestricted (TyUInt 8) emptySurfaceState
  _ <- expectSemanticSuccess
    ( grammarV1CheckedSemanticRefinementType
        staticContext rootScope spellingState sourceType
    )
  (_, activeScope) <- mapLeft show $
    grammarV1BindLocal
      GrammarV1FunctionParameterBinder
      (Located syntheticSpan "v")
      rootScope
  case grammarV1CheckedSemanticRefinementType
      staticContext activeScope emptySurfaceState sourceType of
    Just
      (Left
        (GrammarV1SemanticRefinementBinderScopeError
          (GrammarV1ActiveShadowing shadowing previous))) -> do
            assert (locatedValue shadowing == "v")
              "semantic refinement shadowing diagnostic lost source spelling"
            assert (grammarV1ResolvedBinderDisplayName previous == "v")
              "semantic refinement shadowing diagnostic lost active outer binder"
    other -> Left
      ("active lexical binder did not block refinement shadowing: " <> show other)

semanticRefinementFocusingFailurePreserved :: Either String ()
semanticRefinementFocusingFailurePreserved = do
  sourceType <- oneTypeAliasTarget
    "type Missing = {v : U8 | Missing(v)};"
  case grammarV1CheckedSemanticRefinementType
      emptyStaticContext
      (grammarV1RootLexicalScope (DeclarationKey "decl.SemanticRefinementMissing"))
      emptySurfaceState
      sourceType of
    Just
      (Left
        (GrammarV1SemanticRefinementFocusingError
          (UnknownClaim "Missing"))) -> Right ()
    other -> Left
      ("semantic refinement Core focusing failure changed: " <> show other)

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

expectSemanticSuccess
  :: Maybe
      (Either
        GrammarV1SemanticRefinementTypeError
        (GrammarV1CheckedSemanticRefinementType, scope))
  -> Either String (GrammarV1CheckedSemanticRefinementType, scope)
expectSemanticSuccess result =
  case result of
    Just (Right checked) -> Right checked
    other -> Left ("expected semantic refinement success, got " <> show other)

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

oneTypeAliasTarget :: Text.Text -> Either String GrammarV1Type
oneTypeAliasTarget source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "semantic-refinement" source
  case grammarV1TopLevelDecls sourceFile of
    [topLevel] -> typeAliasTarget topLevel
    declarations -> Left
      ("expected one semantic refinement alias, got " <> show (length declarations))

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values =
  Left ("expected exactly one " <> label <> ", got " <> show (length values))

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
