{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax (Value (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderKind (GrammarV1LetPatternBinder)
  , GrammarV1BinderScopeError (..)
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1BindLocal
  , grammarV1FunctionParameterScope
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1BorrowViewScopeError (..)
  , GrammarV1CheckedBorrowView (..)
  , grammarV1CheckedBorrowViewInScope
  )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..)
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 borrow owner resolves before the view binder exists"
        borrowOwnerPrecedesViewBinding
    , test "SURF-009 borrow view and body lets disappear together at scope exit"
        borrowScopeExitDropsViewAndBodyLets
    , test "SURF-009 sibling borrows may reuse spelling with fresh semantic identities"
        siblingBorrowsReuseSpellingDistinctly
    , test "SURF-009 borrow views cannot shadow active enclosing binders"
        borrowViewCannotShadowOwner
    , test "SURF-009 future borrow views are not visible to the owner expression"
        futureBorrowViewCannotResolveAsOwner
    , test "SURF-009 borrow-view alpha renaming preserves semantic identity"
        borrowViewAlphaRenamingPreservesIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

borrowOwnerPrecedesViewBinding :: Either String ()
borrowOwnerPrecedesViewBinding = do
  functionDecl <- onlyFunction "borrow-prebinding" $ Text.unlines
    [ "fn borrow_scope(owner : U8) -> U8 satisfies C {"
    , "  borrow owner as view { view; };"
    , "  return owner;"
    , "}"
    ]
  (parameters, scope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.BorrowScope") functionDecl)
  ownerBinder <- exactlyOne "borrow owner parameter" parameters
  borrowExpression <- firstExpressionStatement functionDecl
  (checked, finalScope) <- checkedBorrow scope borrowExpression
  assert
    (grammarV1ResolvedBinderKey
      (grammarV1CheckedLocalValueBinder (grammarV1CheckedBorrowOwner checked))
      == grammarV1ResolvedBinderKey ownerBinder)
    "borrow owner did not resolve in the pre-binding parent scope"
  let viewBinder = grammarV1CheckedBorrowViewBinder checked
  assert (grammarV1ResolvedBinderDisplayName viewBinder == "view")
    "borrow view spelling was not retained diagnostically"
  case grammarV1CheckedBorrowBodySteps checked of
    [GrammarV1CheckedLetOccurrenceStep _ occurrence] -> do
      assert
        (grammarV1ResolvedBinderKey (grammarV1CheckedLocalValueBinder occurrence)
          == grammarV1ResolvedBinderKey viewBinder)
        "borrow body did not resolve the exact view binder"
      assert
        (grammarV1CheckedLocalValueCore occurrence
          == VVar (grammarV1ResolvedBinderCoreName viewBinder))
        "borrow body did not use the exact generated view Core name"
    other -> Left ("expected one borrow-body view occurrence, got " <> show other)
  assertNotInScope "view" viewBinder finalScope
  resolvedOwner <- mapLeft show
    (grammarV1ResolveLocal
      (Located (grammarV1ResolvedBinderSourceSpan ownerBinder) "owner")
      finalScope)
  assert
    (grammarV1ResolvedBinderKey resolvedOwner == grammarV1ResolvedBinderKey ownerBinder)
    "borrow scope exit removed or rewrote the enclosing owner binder"

borrowScopeExitDropsViewAndBodyLets :: Either String ()
borrowScopeExitDropsViewAndBodyLets = do
  functionDecl <- onlyFunction "borrow-body-let" $ Text.unlines
    [ "fn borrow_let(owner : U8) -> U8 satisfies C {"
    , "  borrow owner as view {"
    , "    let alias = view;"
    , "    alias;"
    , "  };"
    , "  return owner;"
    , "}"
    ]
  (_, scope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.BorrowLet") functionDecl)
  borrowExpression <- firstExpressionStatement functionDecl
  (checked, finalScope) <- checkedBorrow scope borrowExpression
  let viewBinder = grammarV1CheckedBorrowViewBinder checked
  aliasBinder <- case grammarV1CheckedBorrowBodySteps checked of
    [ GrammarV1CheckedLetBindingStep _ initializer [binder]
      , GrammarV1CheckedLetOccurrenceStep _ returned
      ] -> do
        assert
          (grammarV1ResolvedBinderKey (grammarV1CheckedLocalValueBinder initializer)
            == grammarV1ResolvedBinderKey viewBinder)
          "borrow-body let initializer did not resolve the view binder"
        assert (grammarV1ResolvedBinderDisplayName binder == "alias")
          "borrow-body let binder was not alias"
        assert
          (grammarV1ResolvedBinderKey (grammarV1CheckedLocalValueBinder returned)
            == grammarV1ResolvedBinderKey binder)
          "borrow-body occurrence did not resolve the alias binder"
        Right binder
    other -> Left ("unexpected borrow-body let trace: " <> show other)
  assertNotInScope "view" viewBinder finalScope
  assertNotInScope "alias" aliasBinder finalScope
  let laterName = Located (grammarV1ResolvedBinderSourceSpan aliasBinder) "later"
  (laterBinder, _) <- mapLeft show
    (grammarV1BindLocal GrammarV1LetPatternBinder laterName finalScope)
  assert
    (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey laterBinder) == 3)
    "borrow child-scope exit rewound the declaration-wide binder ordinal"

siblingBorrowsReuseSpellingDistinctly :: Either String ()
siblingBorrowsReuseSpellingDistinctly = do
  functionDecl <- onlyFunction "borrow-siblings" $ Text.unlines
    [ "fn sibling_borrows(owner : U8) -> U8 satisfies C {"
    , "  borrow owner as view { view; };"
    , "  borrow owner as view { view; };"
    , "  return owner;"
    , "}"
    ]
  (_, initialScope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.SiblingBorrows") functionDecl)
  (firstExpression, secondExpression) <- exactlyTwo
    "sibling borrow expressions"
    =<< expressionStatements functionDecl
  (firstChecked, afterFirst) <- checkedBorrow initialScope firstExpression
  (secondChecked, afterSecond) <- checkedBorrow afterFirst secondExpression
  let firstView = grammarV1CheckedBorrowViewBinder firstChecked
      secondView = grammarV1CheckedBorrowViewBinder secondChecked
  assert
    (grammarV1ResolvedBinderDisplayName firstView == "view"
      && grammarV1ResolvedBinderDisplayName secondView == "view")
    "sibling borrow spelling reuse was not retained diagnostically"
  assert
    (grammarV1ResolvedBinderKey firstView /= grammarV1ResolvedBinderKey secondView)
    "sibling borrows reused one semantic binder key"
  assert
    (grammarV1ResolvedBinderCoreName firstView /= grammarV1ResolvedBinderCoreName secondView)
    "sibling borrows reused one generated Core name"
  assert
    (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey firstView) == 1
      && grammarV1BinderOrdinal (grammarV1ResolvedBinderKey secondView) == 2)
    "sibling borrow identities were not allocated monotonically"
  assertNotInScope "view" secondView afterSecond

borrowViewCannotShadowOwner :: Either String ()
borrowViewCannotShadowOwner = do
  functionDecl <- onlyFunction "borrow-shadow" $ Text.unlines
    [ "fn borrow_shadow(owner : U8) -> U8 satisfies C {"
    , "  borrow owner as owner { owner; };"
    , "  return owner;"
    , "}"
    ]
  (_, scope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.BorrowShadow") functionDecl)
  borrowExpression <- firstExpressionStatement functionDecl
  case grammarV1CheckedBorrowViewInScope scope borrowExpression of
    Just (Left (GrammarV1BorrowViewBinderError
      (GrammarV1ActiveShadowing shadowing previous))) -> do
        assert (locatedValue shadowing == "owner")
          "borrow shadowing diagnostic lost the view spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "owner")
          "borrow shadowing diagnostic lost the active owner binder"
    other -> Left ("expected active borrow-view shadow rejection, got " <> show other)

futureBorrowViewCannotResolveAsOwner :: Either String ()
futureBorrowViewCannotResolveAsOwner = do
  functionDecl <- onlyFunction "borrow-future" $ Text.unlines
    [ "fn future_borrow(seed : U8) -> U8 satisfies C {"
    , "  borrow view as view { view; };"
    , "  return seed;"
    , "}"
    ]
  (_, scope) <- mapLeft show
    (grammarV1FunctionParameterScope (DeclarationKey "decl.FutureBorrow") functionDecl)
  borrowExpression <- firstExpressionStatement functionDecl
  case grammarV1CheckedBorrowViewInScope scope borrowExpression of
    Nothing -> Right ()
    other -> Left ("future borrow view leaked into owner resolution: " <> show other)

borrowViewAlphaRenamingPreservesIdentity :: Either String ()
borrowViewAlphaRenamingPreservesIdentity = do
  original <- onlyFunction "borrow-alpha-original" $ Text.unlines
    [ "fn alpha_borrow(owner : U8) -> U8 satisfies C {"
    , "  borrow owner as view { view; };"
    , "  return owner;"
    , "}"
    ]
  renamed <- onlyFunction "borrow-alpha-renamed" $ Text.unlines
    [ "fn alpha_borrow(source : U8) -> U8 satisfies C {"
    , "    borrow source as window { window; };"
    , "    return source;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.AlphaBorrow"
  (originalParameters, originalScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey original)
  (renamedParameters, renamedScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey renamed)
  originalParameter <- exactlyOne "original alpha parameter" originalParameters
  renamedParameter <- exactlyOne "renamed alpha parameter" renamedParameters
  originalExpression <- firstExpressionStatement original
  renamedExpression <- firstExpressionStatement renamed
  (originalChecked, _) <- checkedBorrow originalScope originalExpression
  (renamedChecked, _) <- checkedBorrow renamedScope renamedExpression
  let originalView = grammarV1CheckedBorrowViewBinder originalChecked
      renamedView = grammarV1CheckedBorrowViewBinder renamedChecked
  assert
    (grammarV1ResolvedBinderKey originalParameter
      == grammarV1ResolvedBinderKey renamedParameter)
    "parameter alpha-renaming changed semantic identity"
  assert
    (grammarV1ResolvedBinderKey originalView == grammarV1ResolvedBinderKey renamedView)
    "borrow-view alpha-renaming changed semantic identity"
  assert
    (grammarV1ResolvedBinderCoreName originalView
      == grammarV1ResolvedBinderCoreName renamedView)
    "borrow-view alpha-renaming changed Core identity"
  assert
    (grammarV1ResolvedBinderDisplayName originalView == "view"
      && grammarV1ResolvedBinderDisplayName renamedView == "window")
    "borrow-view alpha spellings were not retained diagnostically"

checkedBorrow
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Either String (GrammarV1CheckedBorrowView, GrammarV1LexicalScope)
checkedBorrow scope expression =
  case grammarV1CheckedBorrowViewInScope scope expression of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked borrow-view scope, got " <> show other)

assertNotInScope
  :: Text.Text
  -> GrammarV1ResolvedBinder
  -> GrammarV1LexicalScope
  -> Either String ()
assertNotInScope displayName binder scope =
  case grammarV1ResolveLocal
      (Located (grammarV1ResolvedBinderSourceSpan binder) displayName)
      scope of
    Left (GrammarV1BinderNotInScope _) -> Right ()
    other -> Left
      ("closed borrow-local binder remained in scope: " <> show other)

firstExpressionStatement
  :: GrammarV1FunctionDecl
  -> Either String (Located GrammarV1Expression)
firstExpressionStatement functionDecl = do
  expressions <- expressionStatements functionDecl
  case expressions of
    first : _ -> Right first
    [] -> Left "expected at least one expression statement"

expressionStatements
  :: GrammarV1FunctionDecl
  -> Either String [Located GrammarV1Expression]
expressionStatements functionDecl =
  Right
    [ expression
    | Located _ (GrammarV1ExpressionStatement expression) <-
        grammarV1BlockStatements (locatedValue (grammarV1FunctionBody functionDecl))
    ]

onlyFunction :: Text.Text -> Text.Text -> Either String GrammarV1FunctionDecl
onlyFunction label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1FunctionDeclaration functionDecl -> Right functionDecl
      other -> Left ("expected function declaration, got " <> show other)
    declarations -> Left
      ("expected one function declaration, got " <> show (length declarations))

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values = Left
  ("expected exactly one " <> label <> ", got " <> show (length values))

exactlyTwo :: String -> [a] -> Either String (a, a)
exactlyTwo _ [first, second] = Right (first, second)
exactlyTwo label values = Left
  ("expected exactly two " <> label <> ", got " <> show (length values))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
