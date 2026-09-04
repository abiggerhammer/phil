{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
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
import Phil.Surface.GrammarV1.SemanticComponentHeader
  ( GrammarV1CheckedSemanticComponentHeader (..)
  , GrammarV1SemanticComponentHeaderError (..)
  , grammarV1CheckedSemanticComponentHeader
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 semantic component headers preserve optional parameter shape"
        optionalParameterShapePreserved
    , test "SURF-009 semantic component headers use generated parameter state"
        generatedParameterState
    , test "SURF-009 semantic component headers are alpha-stable for dependent provides"
        alphaStableDependentProvides
    , test "SURF-009 semantic component headers preserve duplicate-binder diagnostics"
        duplicateBinderPreserved
    , test "SURF-009 semantic component headers preserve Core focusing errors"
        focusingErrorPreserved
    , test "SURF-009 semantic component headers remain bounded to primitive parameters"
        competenceBoundary
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

optionalParameterShapePreserved :: Either String ()
optionalParameterShapePreserved = do
  omitted <- onlyComponent "semantic-component-omitted" "component Omitted {}"
  explicitEmpty <- onlyComponent "semantic-component-explicit" "component Explicit() {}"
  let declarationKey = DeclarationKey "component.optional.lineage"
      definitionRevision = DefinitionRevision "component.optional.v1"
  omittedHeader <- checkedHeader declarationKey definitionRevision omitted
  explicitHeader <- checkedHeader declarationKey definitionRevision explicitEmpty
  assert
    (checkedSemanticComponentParameters omittedHeader == Nothing)
    "omitted component parameter syntax became an explicit telescope"
  assert
    (checkedSemanticComponentParameters explicitHeader == Just [])
    "explicit empty component parameter syntax collapsed to omission"
  assert
    ( checkedSemanticComponentProvidesType omittedHeader == Nothing
      && checkedSemanticComponentProvidesReferences omittedHeader == Nothing )
    "component without provides acquired semantic provides evidence"
  assert
    ( checkedSemanticComponentProvidesType explicitHeader == Nothing
      && checkedSemanticComponentProvidesReferences explicitHeader == Nothing )
    "explicit-empty component without provides acquired semantic provides evidence"
  assert
    (Map.null (stateBindings (checkedSemanticComponentState omittedHeader)))
    "omitted-parameter component acquired a local semantic binding"
  assert
    (Map.null (stateBindings (checkedSemanticComponentState explicitHeader)))
    "explicit-empty component acquired a local semantic binding"

generatedParameterState :: Either String ()
generatedParameterState = do
  component <- onlyComponent "semantic-component-dependent" $ Text.unlines
    [ "component Dependent(n : U8, flag : Bool) provides Bytes[toNat(n)] {"
    , "}"
    ]
  let declarationKey = DeclarationKey "component.semantic.lineage"
      definitionRevision = DefinitionRevision "component.semantic.v1"
  header <- checkedHeader declarationKey definitionRevision component
  case checkedSemanticComponentParameters header of
    Just [(nBinder, TyUInt 8), (flagBinder, TyBool)] -> do
      let nName@(Name nText) = grammarV1ResolvedBinderCoreName nBinder
          flagName@(Name flagText) = grammarV1ResolvedBinderCoreName flagBinder
          state = checkedSemanticComponentState header
          context = resourceContext (stateCore state)
      assert (nText /= "n" && flagText /= "flag")
        "component semantic names collapsed to display spelling"
      assert
        (Map.member nText (stateBindings state) && Map.member flagText (stateBindings state))
        "semantic component SurfaceState omitted generated parameter names"
      assert
        (not (Map.member "n" (stateBindings state)) && not (Map.member "flag" (stateBindings state)))
        "component source spelling leaked into semantic SurfaceState"
      assert
        (Map.member nName (unrestrictedBindings context) && Map.member flagName (unrestrictedBindings context))
        "Core resource context omitted generated component parameter names"
      assert
        (checkedSemanticComponentProvidesType header
          == Just (TyBytes (RefToNat (RefVar nName))))
        "dependent component provides type lost exact semantic n identity"
      references <- maybe
        (Left "present dependent provides type lost reference evidence")
        Right
        (checkedSemanticComponentProvidesReferences header)
      reference <- exactlyOne "component provides reference" references
      assert
        ( grammarV1ResolvedBinderKey
            (grammarV1CheckedLexicalReferenceBinder reference)
          == grammarV1ResolvedBinderKey nBinder )
        "component provides reference did not retain exact n binder evidence"
      assert
        (checkedSemanticComponentDisplayName header == "Dependent")
        "component display name changed on semantic route"
    other -> Left ("unexpected semantic component parameter shape: " <> show other)

alphaStableDependentProvides :: Either String ()
alphaStableDependentProvides = do
  original <- onlyComponent "semantic-component-alpha-original" $ Text.unlines
    [ "component Dependent(n : U8, flag : Bool) provides Bytes[toNat(n)] {"
    , "}"
    ]
  renamed <- onlyComponent "semantic-component-alpha-renamed" $ Text.unlines
    [ "component Dependent(count : U8, ready : Bool) provides Bytes[toNat(count)] {"
    , "}"
    ]
  let declarationKey = DeclarationKey "component.alpha.lineage"
      definitionRevision = DefinitionRevision "component.alpha.v1"
  originalHeader <- checkedHeader declarationKey definitionRevision original
  renamedHeader <- checkedHeader declarationKey definitionRevision renamed
  originalBinders <- parameterBinders originalHeader
  renamedBinders <- parameterBinders renamedHeader
  assert
    (map grammarV1ResolvedBinderKey originalBinders
      == map grammarV1ResolvedBinderKey renamedBinders)
    "alpha-renaming changed component semantic binder keys"
  assert
    (map grammarV1ResolvedBinderCoreName originalBinders
      == map grammarV1ResolvedBinderCoreName renamedBinders)
    "alpha-renaming changed component semantic Core names"
  assert
    (checkedSemanticComponentProvidesType originalHeader
      == checkedSemanticComponentProvidesType renamedHeader)
    "alpha-renaming changed dependent component provides type"
  assert
    (map grammarV1ResolvedBinderDisplayName originalBinders == ["n", "flag"])
    "original component display spellings changed"
  assert
    (map grammarV1ResolvedBinderDisplayName renamedBinders == ["count", "ready"])
    "renamed component display spellings changed"

duplicateBinderPreserved :: Either String ()
duplicateBinderPreserved = do
  component <- onlyComponent "semantic-component-duplicate"
    "component Duplicate(x : U8, x : Bool) {}"
  case grammarV1CheckedSemanticComponentHeader
      emptyStaticContext
      (DeclarationKey "component.duplicate.lineage")
      (DefinitionRevision "component.duplicate.v1")
      component of
    Just (Left (GrammarV1SemanticComponentBinderScopeError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "x")
          "component duplicate diagnostic lost duplicate spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "x")
          "component duplicate diagnostic lost previous binder"
    other -> Left
      ("expected component duplicate-binder rejection, got " <> show other)

focusingErrorPreserved :: Either String ()
focusingErrorPreserved = do
  component <- onlyComponent "semantic-component-focusing"
    "component Bad(x : U8) provides Proof[Missing(x)] {}"
  let actual = grammarV1CheckedSemanticComponentHeader
        emptyStaticContext
        (DeclarationKey "component.focusing.lineage")
        (DefinitionRevision "component.focusing.v1")
        component
  assert
    (actual == Just
      (Left
        (GrammarV1SemanticComponentProvidesFocusingError
          (UnknownClaim "Missing"))))
    ("semantic component route changed Core UnknownClaim rejection: " <> show actual)

competenceBoundary :: Either String ()
competenceBoundary = do
  named <- onlyComponent "semantic-component-named"
    "component Named(x : Other) {}"
  generic <- onlyComponent "semantic-component-generic"
    "component Generic[T : Type](x : U8) {}"
  let check source = grammarV1CheckedSemanticComponentHeader
        emptyStaticContext
        (DeclarationKey "component.boundary.lineage")
        (DefinitionRevision "component.boundary.v1")
        source
  assert (check named == Nothing)
    "nonprimitive component parameter escaped semantic-header competence"
  assert (check generic == Nothing)
    "generic component escaped semantic-header competence"

checkedHeader
  :: DeclarationKey
  -> DefinitionRevision
  -> GrammarV1ComponentDecl
  -> Either String GrammarV1CheckedSemanticComponentHeader
checkedHeader declarationKey definitionRevision component =
  case grammarV1CheckedSemanticComponentHeader
      emptyStaticContext declarationKey definitionRevision component of
    Just (Right (header, [])) -> Right header
    other -> Left ("expected checked semantic component header, got " <> show other)

parameterBinders
  :: GrammarV1CheckedSemanticComponentHeader
  -> Either String [GrammarV1ResolvedBinder]
parameterBinders header = case checkedSemanticComponentParameters header of
  Just parameters -> Right (map fst parameters)
  Nothing -> Left "expected present semantic component parameter telescope"

onlyComponent
  :: Text.Text
  -> Text.Text
  -> Either String GrammarV1ComponentDecl
onlyComponent label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration component -> Right component
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left
      ("expected one component declaration, got " <> show (length declarations))

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
