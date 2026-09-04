{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1ClosureParameterScope
  , grammarV1FunctionParameterScope
  , grammarV1LeaveLexicalScope
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.Parser
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
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

functionAlphaRenamingPreservesSemanticIdentity :: Either String ()
functionAlphaRenamingPreservesSemanticIdentity = do
  original <- onlyFunction "binder-alpha-original" $ Text.unlines
    [ "fn bind(x : U8, y : U8) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  renamed <- onlyFunction "binder-alpha-renamed" $ Text.unlines
    [ "fn bind(left : U8, right : U8) -> U8 satisfies C {"
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
    "different declaration roots reused one Core binder name"

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
