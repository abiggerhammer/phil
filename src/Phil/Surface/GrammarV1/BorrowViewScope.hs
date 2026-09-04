module Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1CheckedBorrowView (..)
  , GrammarV1BorrowViewScopeError (..)
  , grammarV1CheckedBorrowViewInScope
  ) where

import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (GrammarV1BorrowViewBinder)
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1BindLocal
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep
  , GrammarV1LetPatternScopeError
  , grammarV1CheckedLetPatternBlockInScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Bounded lexical result for one source borrow expression. The owner is
-- resolved in the parent scope before the view binder exists. The view and all
-- body-local let binders live in one child frame that is discarded atomically at
-- borrow-body exit, while the declaration-wide fresh-binder ordinal remains
-- advanced for later sibling scopes.
data GrammarV1CheckedBorrowView = GrammarV1CheckedBorrowView
  { grammarV1CheckedBorrowViewSource :: Located GrammarV1Expression
  , grammarV1CheckedBorrowOwner :: GrammarV1CheckedLocalValueOccurrence
  , grammarV1CheckedBorrowViewBinder :: GrammarV1ResolvedBinder
  , grammarV1CheckedBorrowBodySteps :: [GrammarV1CheckedLetScopeStep]
  }
  deriving (Eq, Show)

data GrammarV1BorrowViewScopeError
  = GrammarV1BorrowViewBinderError GrammarV1BinderScopeError
  | GrammarV1BorrowViewBodyError GrammarV1LetPatternScopeError
  deriving (Eq, Show)

-- | Check the lexical boundary of one Grammar-v1 `borrow e as view { ... }`.
-- This route owns binder identity and lexical visibility only. Whether `e` is an
-- affine/linear owner, whether a shared loan is semantically admissible, and
-- whether a returned runtime value contains the borrowed view remain the existing
-- resource/loan checker's responsibility.
grammarV1CheckedBorrowViewInScope
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe
      (Either
        GrammarV1BorrowViewScopeError
        (GrammarV1CheckedBorrowView, GrammarV1LexicalScope))
grammarV1CheckedBorrowViewInScope parentScope source@(Located _ expression) =
  case expression of
    GrammarV1BorrowExpression ownerExpression sourceViewName body -> do
      ownerOccurrence <- grammarV1CheckedLocalValueOccurrenceInScope
        parentScope
        ownerExpression
      let childScope = grammarV1EnterLexicalScope parentScope
      case grammarV1BindLocal
          GrammarV1BorrowViewBinder
          sourceViewName
          childScope of
        Left scopeError ->
          Just (Left (GrammarV1BorrowViewBinderError scopeError))
        Right (viewBinder, boundScope) -> do
          bodyResult <- grammarV1CheckedLetPatternBlockInScope boundScope body
          case bodyResult of
            Left bodyError ->
              Just (Left (GrammarV1BorrowViewBodyError bodyError))
            Right (bodySteps, finalChildScope) ->
              case grammarV1LeaveLexicalScope finalChildScope of
                Left scopeError ->
                  Just (Left (GrammarV1BorrowViewBinderError scopeError))
                Right nextParentScope -> Just (Right
                  ( GrammarV1CheckedBorrowView
                      { grammarV1CheckedBorrowViewSource = source
                      , grammarV1CheckedBorrowOwner = ownerOccurrence
                      , grammarV1CheckedBorrowViewBinder = viewBinder
                      , grammarV1CheckedBorrowBodySteps = bodySteps
                      }
                  , nextParentScope
                  ))
    _ -> Nothing
