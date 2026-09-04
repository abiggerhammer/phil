{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , declareOpaqueClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticCallablePropositions
  ( GrammarV1CheckedSemanticCallableProposition (..)
  , GrammarV1SemanticCallablePropositionError (..)
  , grammarV1CheckedSemanticCallableAssumptions
  , grammarV1CheckedSemanticCallableEnsures
  , grammarV1CheckedSemanticCallableObligations
  , grammarV1CheckedSemanticCallableRequires
  )
import Phil.Surface.GrammarV1.SemanticCallableSignature
  ( GrammarV1SemanticCallableSignatureError (..)
  , GrammarV1SemanticCallableScope (..)
  , grammarV1SemanticCallableParameterScope
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 callable proposition categories use generated semantic names"
        semanticCategoriesUseGeneratedNames
    , test "SURF-009 callable proposition categories preserve source order and category"
        semanticCategoriesPreserveOrder
    , test "SURF-009 callable propositions are alpha-stable at Core identity"
        semanticCallablePropositionsAlphaStable
    , test "SURF-009 callable proposition checking is independent of result-type failure"
        semanticClauseIndependentOfBadResult
    , test "SURF-009 callable proposition Core failures remain explicit"
        semanticCallablePropositionFocusingPreserved
    , test "SURF-009 callable proposition duplicate binder failures remain explicit"
        semanticCallablePropositionDuplicatePreserved
    , test "SURF-009 callable proposition competence remains bounded"
        semanticCallablePropositionCompetenceBoundary
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

semanticCategoriesUseGeneratedNames :: Either String ()
semanticCategoriesUseGeneratedNames = do
  context <- mapLeft show $
    declareOpaqueClaim
      "NeedsNat"
      [(Name "n", SortNat)]
      emptyStaticContext
  source <- onlyCallable "semantic-callable-propositions" $ Text.unlines
    [ "callable Clauses(n : U8, ok : Bool) -> U8 {"
    , "  requires NeedsNat(n);"
    , "  ensures n == n;"
    , "  obligation NeedsNat(n);"
    , "  assumes ok == ok;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticCallableClauses"
  scope <- checkedScope declarationKey source
  case semanticCallableScopeParameters scope of
    [(nBinder, TyUInt 8), (okBinder, TyBool)] -> do
      let nName@(Name nText) = grammarV1ResolvedBinderCoreName nBinder
          okName@(Name okText) = grammarV1ResolvedBinderCoreName okBinder
          state = semanticCallableScopeState scope
          contextState = resourceContext (stateCore state)
      assert (nText /= "n" && okText /= "ok")
        "semantic callable scope reused display spelling"
      assert
        (Map.member nText (stateBindings state) && Map.member okText (stateBindings state))
        "semantic callable scope omitted generated names"
      assert
        (not (Map.member "n" (stateBindings state)) && not (Map.member "ok" (stateBindings state)))
        "source spelling leaked into semantic callable scope"
      assert
        (Map.member nName (unrestrictedBindings contextState)
          && Map.member okName (unrestrictedBindings contextState))
        "Core resource context omitted semantic callable parameters"

      requires <- checkedCategory
        (grammarV1CheckedSemanticCallableRequires context declarationKey source)
      req <- exactlyOne "semantic requires" requires
      assert
        (checkedSemanticCallablePropositionCore req
          == Atom "NeedsNat" [RefToNat (RefVar nName)])
        "requires proposition did not use generated n identity"
      assert
        (checkedSemanticCallablePropositionFocusSteps req
          == [InsertedUIntToNat (RefVar nName)])
        "requires proposition lost exact UInt-to-Nat focusing trace"
      reqRef <- exactlyOne
        "requires lexical reference"
        (checkedSemanticCallablePropositionReferences req)
      assert
        (referenceBinderKey reqRef == grammarV1ResolvedBinderKey nBinder)
        "requires proposition lost exact n binder evidence"

      assumptions <- checkedCategory
        (grammarV1CheckedSemanticCallableAssumptions context declarationKey source)
      assumption <- exactlyOne "semantic assumption" assumptions
      assert
        (checkedSemanticCallablePropositionCore assumption == Truth)
        "reflexive Bool equality did not canonicalize to Truth"
      let assumptionKeys =
            map referenceBinderKey
              (checkedSemanticCallablePropositionReferences assumption)
      assert
        (assumptionKeys
          == replicate 2 (grammarV1ResolvedBinderKey okBinder))
        "assumption occurrences did not retain exact generated ok binder evidence"
    other -> Left ("unexpected semantic callable parameter shape: " <> show other)

semanticCategoriesPreserveOrder :: Either String ()
semanticCategoriesPreserveOrder = do
  context <- mapLeft show $
    declareOpaqueClaim
      "NeedsNat"
      [(Name "n", SortNat)]
      emptyStaticContext
  source <- onlyCallable "semantic-callable-order" $ Text.unlines
    [ "callable Ordered(a : U8, b : U8) -> U8 {"
    , "  requires NeedsNat(a);"
    , "  ensures a == a;"
    , "  requires NeedsNat(b);"
    , "  obligation NeedsNat(a);"
    , "  assumes a == b;"
    , "  obligation NeedsNat(b);"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticCallableOrder"
  scope <- checkedScope declarationKey source
  case semanticCallableScopeParameters scope of
    [(aBinder, _), (bBinder, _)] -> do
      let aName = grammarV1ResolvedBinderCoreName aBinder
          bName = grammarV1ResolvedBinderCoreName bBinder
      requires <- checkedCategory
        (grammarV1CheckedSemanticCallableRequires context declarationKey source)
      assert
        (map checkedSemanticCallablePropositionCore requires
          == [ Atom "NeedsNat" [RefToNat (RefVar aName)]
             , Atom "NeedsNat" [RefToNat (RefVar bName)]
             ])
        "requires category lost source order or semantic identity"
      obligations <- checkedCategory
        (grammarV1CheckedSemanticCallableObligations context declarationKey source)
      assert
        (map checkedSemanticCallablePropositionCore obligations
          == [ Atom "NeedsNat" [RefToNat (RefVar aName)]
             , Atom "NeedsNat" [RefToNat (RefVar bName)]
             ])
        "obligation category lost source order or semantic identity"
      ensures <- checkedCategory
        (grammarV1CheckedSemanticCallableEnsures context declarationKey source)
      assert (length ensures == 1)
        "ensures category was merged with another clause category"
      assumptions <- checkedCategory
        (grammarV1CheckedSemanticCallableAssumptions context declarationKey source)
      assert (length assumptions == 1)
        "assumption category was merged with another clause category"
    other -> Left ("unexpected ordered parameter shape: " <> show other)

semanticCallablePropositionsAlphaStable :: Either String ()
semanticCallablePropositionsAlphaStable = do
  original <- onlyCallable "semantic-callable-prop-alpha-original"
    "callable Alpha(x : U8) -> U8 { ensures x == x; }"
  renamed <- onlyCallable "semantic-callable-prop-alpha-renamed"
    "callable Alpha(count : U8) -> U8 { ensures count == count; }"
  let declarationKey = DeclarationKey "decl.SemanticCallablePropAlpha"
  originalChecked <- checkedCategory
    (grammarV1CheckedSemanticCallableEnsures
      emptyStaticContext declarationKey original)
  renamedChecked <- checkedCategory
    (grammarV1CheckedSemanticCallableEnsures
      emptyStaticContext declarationKey renamed)
  originalOne <- exactlyOne "original alpha ensures" originalChecked
  renamedOne <- exactlyOne "renamed alpha ensures" renamedChecked
  assert
    (checkedSemanticCallablePropositionCore originalOne
      == checkedSemanticCallablePropositionCore renamedOne)
    "alpha-renaming changed callable proposition Core meaning"
  let originalKeys =
        map referenceBinderKey
          (checkedSemanticCallablePropositionReferences originalOne)
      renamedKeys =
        map referenceBinderKey
          (checkedSemanticCallablePropositionReferences renamedOne)
  assert (length originalKeys == 2 && length renamedKeys == 2)
    "reflexive equality did not retain both lexical occurrence records"
  assert (originalKeys == renamedKeys)
    "alpha-renaming changed callable proposition binder identity"

semanticClauseIndependentOfBadResult :: Either String ()
semanticClauseIndependentOfBadResult = do
  source <- onlyCallable "semantic-callable-bad-result"
    "callable Independent(x : U8) -> Proof[Missing(x)] { ensures x == x; }"
  let declarationKey = DeclarationKey "decl.SemanticCallableIndependent"
  ensures <- checkedCategory
    (grammarV1CheckedSemanticCallableEnsures
      emptyStaticContext declarationKey source)
  checked <- exactlyOne "independent ensures" ensures
  scope <- checkedScope declarationKey source
  binder <- exactlyOne
    "independent parameter"
    (map fst (semanticCallableScopeParameters scope))
  assert
    (checkedSemanticCallablePropositionCore checked == Truth)
    "bad result type poisoned independent ensures canonical meaning"
  assert
    ( map referenceBinderKey
        (checkedSemanticCallablePropositionReferences checked)
      == replicate 2 (grammarV1ResolvedBinderKey binder) )
    "bad result type changed independent ensures binder evidence"

semanticCallablePropositionFocusingPreserved :: Either String ()
semanticCallablePropositionFocusingPreserved = do
  source <- onlyCallable "semantic-callable-prop-focusing"
    "callable Bad(x : U8) -> U8 { ensures Missing(x); }"
  let actual = grammarV1CheckedSemanticCallableEnsures
        emptyStaticContext
        (DeclarationKey "decl.SemanticCallablePropFocusing")
        source
  case actual of
    Just (Left (GrammarV1SemanticCallablePropositionFocusingError _
      (UnknownClaim "Missing"))) -> Right ()
    other -> Left ("semantic callable proposition changed UnknownClaim: " <> show other)

semanticCallablePropositionDuplicatePreserved :: Either String ()
semanticCallablePropositionDuplicatePreserved = do
  source <- onlyCallable "semantic-callable-prop-duplicate"
    "callable Duplicate(x : U8, x : Bool) -> U8 { ensures true; }"
  let actual = grammarV1CheckedSemanticCallableEnsures
        emptyStaticContext
        (DeclarationKey "decl.SemanticCallablePropDuplicate")
        source
  case actual of
    Just (Left (GrammarV1SemanticCallablePropositionScopeError
      (GrammarV1SemanticCallableBinderScopeError
        (GrammarV1DuplicateBinder duplicate previous)))) -> do
          assert (locatedValue duplicate == "x")
            "semantic proposition duplicate diagnostic lost source spelling"
          assert (grammarV1ResolvedBinderDisplayName previous == "x")
            "semantic proposition duplicate diagnostic lost prior binder"
    other -> Left ("expected duplicate-binder proposition rejection, got " <> show other)

semanticCallablePropositionCompetenceBoundary :: Either String ()
semanticCallablePropositionCompetenceBoundary = do
  generic <- onlyCallable "semantic-callable-prop-generic"
    "callable Generic[T : Type](x : U8) -> U8 { ensures x == x; }"
  named <- onlyCallable "semantic-callable-prop-named"
    "callable Named(x : Other) -> U8 { ensures true; }"
  unresolved <- onlyCallable "semantic-callable-prop-unresolved"
    "callable Unresolved(x : U8) -> U8 { ensures missing == missing; }"
  let declarationKey = DeclarationKey "decl.SemanticCallablePropBoundary"
      check source = grammarV1CheckedSemanticCallableEnsures
        emptyStaticContext declarationKey source
  assert (check generic == Nothing)
    "generic callable escaped semantic proposition competence"
  assert (check named == Nothing)
    "nonprimitive callable parameter escaped semantic proposition competence"
  case check unresolved of
    Just (Left (GrammarV1SemanticCallablePropositionCheckNonCompetent _)) -> Right ()
    other -> Left
      ("unresolved global-looking proposition did not remain explicit check non-competence: "
        <> show other)

referenceBinderKey :: GrammarV1CheckedLexicalReference -> GrammarV1BinderKey
referenceBinderKey =
  grammarV1ResolvedBinderKey . grammarV1CheckedLexicalReferenceBinder

checkedScope
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either String GrammarV1SemanticCallableScope
checkedScope declarationKey source =
  case grammarV1SemanticCallableParameterScope declarationKey source of
    Just (Right scope) -> Right scope
    other -> Left ("expected semantic callable parameter scope, got " <> show other)

checkedCategory
  :: Maybe
      (Either
        GrammarV1SemanticCallablePropositionError
        [GrammarV1CheckedSemanticCallableProposition])
  -> Either String [GrammarV1CheckedSemanticCallableProposition]
checkedCategory actual = case actual of
  Just (Right checked) -> Right checked
  other -> Left ("expected checked semantic callable proposition category, got " <> show other)

onlyCallable
  :: Text.Text
  -> Text.Text
  -> Either String GrammarV1CallableContractDecl
onlyCallable label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1CallableContractDeclaration callable -> Right callable
        other -> Left ("expected callable declaration, got " <> show other)
    declarations -> Left
      ("expected one callable declaration, got " <> show (length declarations))

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values = Left
  ("expected exactly one " <> label <> ", got " <> show (length values))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
