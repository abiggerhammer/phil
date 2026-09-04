{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1ClosureParameterScope
  , grammarV1FunctionParameterScope
  , grammarV1LeaveLexicalScope
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , GrammarV1CheckedParameterBody (..)
  , GrammarV1ParameterBodyError (..)
  , grammarV1CheckedClosureParameterBody
  , grammarV1CheckedFunctionParameterBody
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticFunctionHeader
  ( GrammarV1CheckedSemanticFunctionHeader (..)
  , GrammarV1SemanticFunctionHeaderError (..)
  , grammarV1CheckedSemanticFunctionHeader
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 function binder identity is independent of alpha spelling and source span"
        functionAlphaRenamingPreservesSemanticIdentity
    , test "SURF-009 duplicate function parameter binders reject"
        duplicateFunctionParameterRejects
    , test "SURF-009 active closure parameter shadowing rejects"
        activeClosureShadowingRejects
    , test "SURF-009 sibling lexical scopes may reuse spelling with fresh identity"
        siblingScopesReuseSpellingDistinctly
    , test "SURF-009 declaration roots keep equal local ordinals distinct"
        declarationRootsSeparateBinderIdentity
    , test "SURF-009 function body parameter occurrences keep alpha-stable semantic identity"
        functionBodyParameterOccurrencesResolve
    , test "SURF-009 closure body resolves enclosing and local parameters to exact occurrences"
        closureBodyResolvesOuterAndLocalParameters
    , test "SURF-009 unknown bare body names remain outside local-binder competence"
        unknownBodyNameRemainsOutsideCompetence
    , test "SURF-009 let-bound bodies remain for the later pattern-binder slice"
        letBodyRemainsOutsideCompetence
    , test "SURF-009 body route preserves duplicate-parameter rejection"
        parameterBodyPreservesDuplicateRejection
    , test "SURF-009 semantic function headers use generated parameter state"
        semanticFunctionHeaderUsesGeneratedNames
    , test "SURF-009 semantic function headers are alpha-stable for dependent results"
        semanticFunctionHeaderAlphaStable
    , test "SURF-009 semantic function headers preserve duplicate-binder diagnostics"
        semanticFunctionHeaderDuplicatePreserved
    , test "SURF-009 semantic function headers preserve Core focusing errors"
        semanticFunctionHeaderFocusingPreserved
    , test "SURF-009 semantic function headers remain bounded to primitive parameters"
        semanticFunctionHeaderCompetenceBoundary
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

functionAlphaRenamingPreservesSemanticIdentity :: Either String ()
functionAlphaRenamingPreservesSemanticIdentity = do
  original <- onlyFunction "binder-alpha-original" $ Text.unlines
    [ "fn alpha_scope(x : U8, y : U8) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  renamed <- onlyFunction "binder-alpha-renamed" $ Text.unlines
    [ "fn alpha_scope(left : U8, right : U8) -> U8 satisfies C {"
    , "    return left;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.Bind"
  (originalBinders, _) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey original)
  (renamedBinders, _) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey renamed)
  assert
    (map grammarV1ResolvedBinderKey originalBinders
      == map grammarV1ResolvedBinderKey renamedBinders)
    "alpha-renaming changed semantic binder keys"
  assert
    (map grammarV1ResolvedBinderCoreName originalBinders
      == map grammarV1ResolvedBinderCoreName renamedBinders)
    "alpha-renaming changed Core binder names"
  assert
    (map grammarV1ResolvedBinderDisplayName originalBinders == ["x", "y"])
    "original display spellings were not retained diagnostically"
  assert
    (map grammarV1ResolvedBinderDisplayName renamedBinders == ["left", "right"])
    "renamed display spellings were not retained diagnostically"
  assert
    (map grammarV1ResolvedBinderSourceSpan originalBinders
      /= map grammarV1ResolvedBinderSourceSpan renamedBinders)
    "test did not actually vary source spans"

duplicateFunctionParameterRejects :: Either String ()
duplicateFunctionParameterRejects = do
  functionDecl <- onlyFunction "binder-duplicate" $ Text.unlines
    [ "fn bad(x : U8, x : U8) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  case grammarV1FunctionParameterScope (DeclarationKey "decl.Bad") functionDecl of
    Left (GrammarV1DuplicateBinder duplicate previous) -> do
      assert (locatedValue duplicate == "x")
        "duplicate diagnostic lost source spelling"
      assert (grammarV1ResolvedBinderDisplayName previous == "x")
        "duplicate diagnostic lost the first active binder"
    other -> Left ("expected duplicate binder rejection, got " <> show other)

activeClosureShadowingRejects :: Either String ()
activeClosureShadowingRejects = do
  outerFunction <- onlyFunction "binder-outer" $ Text.unlines
    [ "fn outer(x : U8) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  closure <- onlyClosure "binder-shadow-closure" $ Text.unlines
    [ "component Holder() {"
    , "  closure (x : U8) satisfies C { return x; };"
    , "}"
    ]
  (_, outerScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.Outer") outerFunction)
  case grammarV1ClosureParameterScope outerScope closure of
    Left (GrammarV1ActiveShadowing shadowing previous) -> do
      assert (locatedValue shadowing == "x")
        "shadowing diagnostic lost closure parameter spelling"
      assert (grammarV1ResolvedBinderDisplayName previous == "x")
        "shadowing diagnostic lost enclosing active binder"
    other -> Left ("expected active-shadowing rejection, got " <> show other)

siblingScopesReuseSpellingDistinctly :: Either String ()
siblingScopesReuseSpellingDistinctly = do
  outerFunction <- onlyFunction "binder-sibling-outer" $ Text.unlines
    [ "fn outer(seed : U8) -> U8 satisfies C {"
    , "  return seed;"
    , "}"
    ]
  closure <- onlyClosure "binder-sibling-closure" $ Text.unlines
    [ "component Holder() {"
    , "  closure (item : U8) satisfies C { return item; };"
    , "}"
    ]
  parameterName <- onlyClosureParameterName closure
  (_, outerScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.Siblings") outerFunction)

  (firstBinders, firstChild) <- mapLeft show
    (grammarV1ClosureParameterScope outerScope closure)
  firstBinder <- exactlyOne "first sibling binder" firstBinders
  resolvedFirst <- mapLeft show (grammarV1ResolveLocal parameterName firstChild)
  assert (grammarV1ResolvedBinderKey resolvedFirst == grammarV1ResolvedBinderKey firstBinder)
    "first sibling binder did not resolve to its exact semantic occurrence"
  afterFirst <- mapLeft show (grammarV1LeaveLexicalScope firstChild)
  case grammarV1ResolveLocal parameterName afterFirst of
    Left (GrammarV1BinderNotInScope missing) ->
      assert (locatedValue missing == "item")
        "scope-exit diagnostic lost source spelling"
    other -> Left ("closed sibling binder remained in scope: " <> show other)

  (secondBinders, secondChild) <- mapLeft show
    (grammarV1ClosureParameterScope afterFirst closure)
  secondBinder <- exactlyOne "second sibling binder" secondBinders
  assert
    (grammarV1ResolvedBinderKey firstBinder /= grammarV1ResolvedBinderKey secondBinder)
    "disjoint sibling binders reused one semantic key"
  assert
    (grammarV1ResolvedBinderCoreName firstBinder
      /= grammarV1ResolvedBinderCoreName secondBinder)
    "disjoint sibling binders reused one Core name"
  assert
    (grammarV1ResolvedBinderDisplayName secondBinder == "item")
    "sibling spelling reuse was not preserved diagnostically"
  _ <- mapLeft show (grammarV1ResolveLocal parameterName secondChild)
  Right ()

declarationRootsSeparateBinderIdentity :: Either String ()
declarationRootsSeparateBinderIdentity = do
  functionDecl <- onlyFunction "binder-root-separation" $ Text.unlines
    [ "fn same(x : U8) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  (leftBinders, _) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.Left") functionDecl)
  (rightBinders, _) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.Right") functionDecl)
  leftBinder <- exactlyOne "left-root binder" leftBinders
  rightBinder <- exactlyOne "right-root binder" rightBinders
  assert
    (grammarV1ResolvedBinderKey leftBinder /= grammarV1ResolvedBinderKey rightBinder)
    "different declaration roots reused one semantic binder key"
  assert
    (grammarV1ResolvedBinderCoreName leftBinder
      /= grammarV1ResolvedBinderCoreName rightBinder)
    "different declaration roots reused one Core name"

functionBodyParameterOccurrencesResolve :: Either String ()
functionBodyParameterOccurrencesResolve = do
  original <- onlyFunction "binder-body-original" $ Text.unlines
    [ "fn body_scope(x : U8, y : U8) -> U8 satisfies C {"
    , "  x;"
    , "  return (y);"
    , "}"
    ]
  renamed <- onlyFunction "binder-body-renamed" $ Text.unlines
    [ "fn body_scope(left : U8, right : U8) -> U8 satisfies C {"
    , "    left;"
    , "    return ((right));"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.BodyScope"
  originalChecked <- checkedFunctionBody declarationKey original
  renamedChecked <- checkedFunctionBody declarationKey renamed
  assert
    (bodyOccurrenceKeys originalChecked == bodyOccurrenceKeys renamedChecked)
    "alpha-renaming changed resolved body occurrence identity"
  assert
    (bodyCoreValues originalChecked == expectedBinderCoreValues originalChecked)
    "original body occurrences did not use exact generated Core names"
  assert
    (bodyCoreValues renamedChecked == expectedBinderCoreValues renamedChecked)
    "renamed body occurrences did not use exact generated Core names"
  assert
    (map grammarV1ResolvedBinderDisplayName
      (grammarV1CheckedParameterBinders originalChecked) == ["x", "y"])
    "original body binder display spellings were not preserved diagnostically"
  assert
    (map grammarV1ResolvedBinderDisplayName
      (grammarV1CheckedParameterBinders renamedChecked) == ["left", "right"])
    "renamed body binder display spellings were not preserved diagnostically"

closureBodyResolvesOuterAndLocalParameters :: Either String ()
closureBodyResolvesOuterAndLocalParameters = do
  outerFunction <- onlyFunction "binder-body-outer" $ Text.unlines
    [ "fn outer_scope(seed : U8) -> U8 satisfies C {"
    , "  return seed;"
    , "}"
    ]
  closure <- onlyClosure "binder-body-closure" $ Text.unlines
    [ "component Holder() {"
    , "  closure (item : U8) satisfies C {"
    , "    seed;"
    , "    return (item);"
    , "  };"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.ClosureBody"
  (outerBinders, outerScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey outerFunction)
  outerBinder <- exactlyOne "outer parameter binder" outerBinders
  checked <- case grammarV1CheckedClosureParameterBody outerScope closure of
    Just (Right body) -> Right body
    other -> Left ("expected checked closure parameter body, got " <> show other)
  localBinder <- exactlyOne
    "closure parameter binder"
    (grammarV1CheckedParameterBinders checked)
  assert
    (bodyOccurrenceKeys checked
      == [ grammarV1ResolvedBinderKey outerBinder
         , grammarV1ResolvedBinderKey localBinder
         ])
    "closure body did not resolve outer then local parameter occurrences exactly"
  assert
    (bodyCoreValues checked
      == [ VVar (grammarV1ResolvedBinderCoreName outerBinder)
         , VVar (grammarV1ResolvedBinderCoreName localBinder)
         ])
    "closure body Core values did not preserve exact outer/local binder names"

unknownBodyNameRemainsOutsideCompetence :: Either String ()
unknownBodyNameRemainsOutsideCompetence = do
  functionDecl <- onlyFunction "binder-body-global" $ Text.unlines
    [ "fn global_scope(x : U8) -> U8 satisfies C {"
    , "  return helper;"
    , "}"
    ]
  case grammarV1CheckedFunctionParameterBody
      (DeclarationKey "decl.GlobalScope") functionDecl of
    Nothing -> Right ()
    other -> Left ("unknown bare name was misclassified as a local binder: " <> show other)

letBodyRemainsOutsideCompetence :: Either String ()
letBodyRemainsOutsideCompetence = do
  functionDecl <- onlyFunction "binder-body-let" $ Text.unlines
    [ "fn let_scope(x : U8) -> U8 satisfies C {"
    , "  let y = x;"
    , "  return y;"
    , "}"
    ]
  case grammarV1CheckedFunctionParameterBody
      (DeclarationKey "decl.LetScope") functionDecl of
    Nothing -> Right ()
    other -> Left ("let-bound body escaped the later pattern-binder slice: " <> show other)

parameterBodyPreservesDuplicateRejection :: Either String ()
parameterBodyPreservesDuplicateRejection = do
  functionDecl <- onlyFunction "binder-body-duplicate" $ Text.unlines
    [ "fn duplicate_scope(x : U8, x : U8) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  case grammarV1CheckedFunctionParameterBody
      (DeclarationKey "decl.DuplicateScope") functionDecl of
    Just (Left (GrammarV1ParameterBodyBinderError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "x")
          "body duplicate diagnostic lost duplicate spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "x")
          "body duplicate diagnostic lost previous binder"
    other -> Left ("expected body duplicate-binder rejection, got " <> show other)

semanticFunctionHeaderUsesGeneratedNames :: Either String ()
semanticFunctionHeaderUsesGeneratedNames = do
  functionDecl <- onlyFunction "semantic-function-header" $ Text.unlines
    [ "fn dependent(x : U8, flag : Bool) -> Bytes[toNat(x)] satisfies C {"
    , "  return x;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticFunction"
      definitionRevision = DefinitionRevision "def.SemanticFunction.v1"
  header <- checkedSemanticFunctionHeader
    declarationKey definitionRevision functionDecl
  case checkedSemanticFunctionParameters header of
    [(xBinder, TyUInt 8), (flagBinder, TyBool)] -> do
      let xName@(Name xText) = grammarV1ResolvedBinderCoreName xBinder
          flagName@(Name flagText) = grammarV1ResolvedBinderCoreName flagBinder
          state = checkedSemanticFunctionState header
          context = resourceContext (stateCore state)
      assert (xText /= "x" && flagText /= "flag")
        "semantic parameter names collapsed to source spelling"
      assert
        ( Map.member xText (stateBindings state)
          && Map.member flagText (stateBindings state) )
        "semantic SurfaceState omitted generated function parameter names"
      assert
        ( not (Map.member "x" (stateBindings state))
          && not (Map.member "flag" (stateBindings state)) )
        "source parameter spelling leaked into semantic SurfaceState"
      assert
        ( Map.member xName (unrestrictedBindings context)
          && Map.member flagName (unrestrictedBindings context) )
        "Core resource context omitted generated function parameter names"
      assert
        (checkedSemanticFunctionResultType header
          == TyBytes (RefToNat (RefVar xName)))
        "dependent function result did not retain generated x identity"
      reference <- exactlyOne
        "semantic function result reference"
        (checkedSemanticFunctionResultReferences header)
      assert
        ( grammarV1ResolvedBinderKey
            (grammarV1CheckedLexicalReferenceBinder reference)
          == grammarV1ResolvedBinderKey xBinder )
        "dependent result reference did not retain exact x binder evidence"
      assert
        (checkedSemanticFunctionSatisfiesReference header
          == ReferencedGenericStaticActual "C")
        "semantic function header changed the unresolved satisfies reference"
    other -> Left ("unexpected semantic parameter shape: " <> show other)

semanticFunctionHeaderAlphaStable :: Either String ()
semanticFunctionHeaderAlphaStable = do
  original <- onlyFunction "semantic-function-alpha-original" $ Text.unlines
    [ "fn dependent(x : U8, flag : Bool) -> Bytes[toNat(x)] satisfies C {"
    , "  return x;"
    , "}"
    ]
  renamed <- onlyFunction "semantic-function-alpha-renamed" $ Text.unlines
    [ "fn dependent(count : U8, ready : Bool) -> Bytes[toNat(count)] satisfies C {"
    , "    return count;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticAlpha"
      definitionRevision = DefinitionRevision "def.SemanticAlpha.v1"
  originalHeader <- checkedSemanticFunctionHeader
    declarationKey definitionRevision original
  renamedHeader <- checkedSemanticFunctionHeader
    declarationKey definitionRevision renamed
  let originalBinders = map fst (checkedSemanticFunctionParameters originalHeader)
      renamedBinders = map fst (checkedSemanticFunctionParameters renamedHeader)
  assert
    (map grammarV1ResolvedBinderCoreName originalBinders
      == map grammarV1ResolvedBinderCoreName renamedBinders)
    "alpha-renaming changed semantic function parameter Core names"
  assert
    (map grammarV1ResolvedBinderKey originalBinders
      == map grammarV1ResolvedBinderKey renamedBinders)
    "alpha-renaming changed semantic function parameter keys"
  assert
    (checkedSemanticFunctionResultType originalHeader
      == checkedSemanticFunctionResultType renamedHeader)
    "alpha-renaming changed dependent semantic function result type"
  assert
    (map grammarV1ResolvedBinderDisplayName originalBinders == ["x", "flag"])
    "original semantic function parameter display names changed"
  assert
    (map grammarV1ResolvedBinderDisplayName renamedBinders == ["count", "ready"])
    "renamed semantic function parameter display names changed"

semanticFunctionHeaderDuplicatePreserved :: Either String ()
semanticFunctionHeaderDuplicatePreserved = do
  functionDecl <- onlyFunction "semantic-function-duplicate" $ Text.unlines
    [ "fn duplicate(x : U8, x : Bool) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  case grammarV1CheckedSemanticFunctionHeader
      emptyStaticContext
      (DeclarationKey "decl.SemanticDuplicate")
      (DefinitionRevision "def.SemanticDuplicate.v1")
      functionDecl of
    Just (Left (GrammarV1SemanticFunctionBinderScopeError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "x")
          "semantic header duplicate diagnostic lost source spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "x")
          "semantic header duplicate diagnostic lost previous binder"
    other -> Left
      ("expected semantic-header duplicate-binder rejection, got " <> show other)

semanticFunctionHeaderFocusingPreserved :: Either String ()
semanticFunctionHeaderFocusingPreserved = do
  functionDecl <- onlyFunction "semantic-function-focusing" $ Text.unlines
    [ "fn bad(x : U8) -> Proof[Missing(x)] satisfies C {"
    , "  return x;"
    , "}"
    ]
  let actual = grammarV1CheckedSemanticFunctionHeader
        emptyStaticContext
        (DeclarationKey "decl.SemanticFocusing")
        (DefinitionRevision "def.SemanticFocusing.v1")
        functionDecl
  assert
    (actual == Just
      (Left
        (GrammarV1SemanticFunctionResultFocusingError
          (UnknownClaim "Missing"))))
    ("semantic header changed Core UnknownClaim rejection: " <> show actual)

semanticFunctionHeaderCompetenceBoundary :: Either String ()
semanticFunctionHeaderCompetenceBoundary = do
  named <- onlyFunction "semantic-function-named" $ Text.unlines
    [ "fn named(x : Other) -> U8 satisfies C {"
    , "  return 1;"
    , "}"
    ]
  generic <- onlyFunction "semantic-function-generic" $ Text.unlines
    [ "fn generic[T : Type](x : U8) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  let check source = grammarV1CheckedSemanticFunctionHeader
        emptyStaticContext
        (DeclarationKey "decl.SemanticBoundary")
        (DefinitionRevision "def.SemanticBoundary.v1")
        source
  assert (check named == Nothing)
    "nonprimitive parameter escaped semantic-header competence"
  assert (check generic == Nothing)
    "generic function escaped semantic-header competence"

checkedFunctionBody
  :: DeclarationKey
  -> GrammarV1FunctionDecl
  -> Either String GrammarV1CheckedParameterBody
checkedFunctionBody declarationKey functionDecl =
  case grammarV1CheckedFunctionParameterBody declarationKey functionDecl of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked function parameter body, got " <> show other)

checkedSemanticFunctionHeader
  :: DeclarationKey
  -> DefinitionRevision
  -> GrammarV1FunctionDecl
  -> Either String GrammarV1CheckedSemanticFunctionHeader
checkedSemanticFunctionHeader declarationKey definitionRevision functionDecl =
  case grammarV1CheckedSemanticFunctionHeader
      emptyStaticContext declarationKey definitionRevision functionDecl of
    Just (Right (header, [])) -> Right header
    other -> Left ("expected checked semantic function header, got " <> show other)

bodyOccurrenceKeys :: GrammarV1CheckedParameterBody -> [GrammarV1BinderKey]
bodyOccurrenceKeys =
  map (grammarV1ResolvedBinderKey . grammarV1CheckedLocalValueBinder)
    . grammarV1CheckedParameterOccurrences

bodyCoreValues :: GrammarV1CheckedParameterBody -> [Value]
bodyCoreValues =
  map grammarV1CheckedLocalValueCore . grammarV1CheckedParameterOccurrences

expectedBinderCoreValues :: GrammarV1CheckedParameterBody -> [Value]
expectedBinderCoreValues =
  map (VVar . grammarV1ResolvedBinderCoreName) . grammarV1CheckedParameterBinders

onlyFunction :: Text.Text -> Text.Text -> Either String GrammarV1FunctionDecl
onlyFunction label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1FunctionDeclaration functionDecl -> Right functionDecl
      other -> Left ("expected function declaration, got " <> show other)
    declarations -> Left
      ("expected one function declaration, got " <> show (length declarations))

onlyClosure :: Text.Text -> Text.Text -> Either String GrammarV1Closure
onlyClosure label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
          [Located _ (GrammarV1ExpressionStatement expression)] ->
            closureFromExpression expression
          statements -> Left
            ("expected one closure-bearing statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left
      ("expected one component declaration, got " <> show (length declarations))

closureFromExpression
  :: Located GrammarV1Expression
  -> Either String GrammarV1Closure
closureFromExpression (Located _ expression) = case expression of
  GrammarV1ClosureExpression closure -> Right closure
  other -> Left ("expected closure expression, got " <> show other)

onlyClosureParameterName
  :: GrammarV1Closure
  -> Either String (Located Text.Text)
onlyClosureParameterName closure = case grammarV1ClosureTermParams closure of
  [Located _ parameter] -> Right (grammarV1TermParamName parameter)
  parameters -> Left
    ("expected one closure parameter, got " <> show (length parameters))

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
