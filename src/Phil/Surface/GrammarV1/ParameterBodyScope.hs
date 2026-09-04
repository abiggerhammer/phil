module Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , GrammarV1CheckedParameterBody (..)
  , GrammarV1ParameterBodyError (..)
  , grammarV1CheckedLocalValueOccurrenceInScope
  , grammarV1CheckedFunctionParameterBody
  , grammarV1CheckedClosureParameterBody
  ) where

import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Value (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..)
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1ClosureParameterScope
  , grammarV1FunctionParameterScope
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1Closure (..)
  , GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | One source name occurrence that has been resolved to exact semantic binder
-- identity. The Core value is keyed by the binder's generated Core Name, never by
-- source spelling or source position.
data GrammarV1CheckedLocalValueOccurrence = GrammarV1CheckedLocalValueOccurrence
  { grammarV1CheckedLocalValueSource :: Located GrammarV1Expression
  , grammarV1CheckedLocalValueBinder :: GrammarV1ResolvedBinder
  , grammarV1CheckedLocalValueCore :: Value
  }
  deriving (Eq, Show)

-- | Bounded body result for the first SURF-009 migration slice. Parameter binders
-- and all admitted body occurrences remain explicit so later body elaboration can
-- consume exact binder evidence instead of reconstructing identity from spelling.
data GrammarV1CheckedParameterBody = GrammarV1CheckedParameterBody
  { grammarV1CheckedParameterBinders :: [GrammarV1ResolvedBinder]
  , grammarV1CheckedParameterOccurrences :: [GrammarV1CheckedLocalValueOccurrence]
  }
  deriving (Eq, Show)

newtype GrammarV1ParameterBodyError = GrammarV1ParameterBodyBinderError
  { grammarV1ParameterBodyBinderError :: GrammarV1BinderScopeError
  }
  deriving (Eq, Show)

-- | Resolve the bounded function-body fragment in which every statement is a
-- bare or parenthesized local parameter value occurrence. Unknown bare names stay
-- outside competence because they may denote static/global declarations; calls,
-- qualified references, static applications, let/pattern binders, and richer
-- expressions are likewise deferred to later SURF-009/body slices.
grammarV1CheckedFunctionParameterBody
  :: DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1ParameterBodyError GrammarV1CheckedParameterBody)
grammarV1CheckedFunctionParameterBody declarationKey functionDecl =
  case grammarV1FunctionParameterScope declarationKey functionDecl of
    Left scopeError -> Just (Left (GrammarV1ParameterBodyBinderError scopeError))
    Right (binders, scope) ->
      fmap
        (Right . GrammarV1CheckedParameterBody binders)
        (checkedBlockOccurrences scope (grammarV1FunctionBody functionDecl))

-- | Resolve the same bounded fragment for one closure. The supplied outer scope
-- remains active, so lexical references to enclosing parameters resolve to their
-- exact outer binder while closure parameters receive fresh child-scope identity.
-- This establishes lexical visibility only; capture ownership/admissibility stays
-- with the callable/closure contract rather than being inferred here.
grammarV1CheckedClosureParameterBody
  :: GrammarV1LexicalScope
  -> GrammarV1Closure
  -> Maybe (Either GrammarV1ParameterBodyError GrammarV1CheckedParameterBody)
grammarV1CheckedClosureParameterBody outerScope closure =
  case grammarV1ClosureParameterScope outerScope closure of
    Left scopeError -> Just (Left (GrammarV1ParameterBodyBinderError scopeError))
    Right (binders, scope) ->
      fmap
        (Right . GrammarV1CheckedParameterBody binders)
        (checkedBlockOccurrences scope (grammarV1ClosureBody closure))

checkedBlockOccurrences
  :: GrammarV1LexicalScope
  -> Located GrammarV1Block
  -> Maybe [GrammarV1CheckedLocalValueOccurrence]
checkedBlockOccurrences scope (Located _ (GrammarV1Block statements)) =
  mapM (checkedStatementOccurrence scope) statements

checkedStatementOccurrence
  :: GrammarV1LexicalScope
  -> Located GrammarV1Statement
  -> Maybe GrammarV1CheckedLocalValueOccurrence
checkedStatementOccurrence scope (Located _ statement) = case statement of
  GrammarV1ReturnStatement expression ->
    grammarV1CheckedLocalValueOccurrenceInScope scope expression
  GrammarV1ExpressionStatement expression ->
    grammarV1CheckedLocalValueOccurrenceInScope scope expression
  GrammarV1LetStatement _ _ -> Nothing

-- | Resolve one bare or parenthesized single-segment local value occurrence in an
-- exact lexical scope. An absent local stays outside this bounded route because
-- the same source spelling may instead denote a static/global declaration.
grammarV1CheckedLocalValueOccurrenceInScope
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe GrammarV1CheckedLocalValueOccurrence
grammarV1CheckedLocalValueOccurrenceInScope scope source@(Located expressionSpan expression) =
  case expression of
    GrammarV1ParenthesizedExpression inner ->
      grammarV1CheckedLocalValueOccurrenceInScope scope inner
    GrammarV1NameExpression reference arguments
      | null arguments
      , null (grammarV1StaticReferenceArguments reference)
      , [displayName] <- grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) ->
          case grammarV1ResolveLocal (Located expressionSpan displayName) scope of
            Right resolvedBinder -> Just GrammarV1CheckedLocalValueOccurrence
              { grammarV1CheckedLocalValueSource = source
              , grammarV1CheckedLocalValueBinder = resolvedBinder
              , grammarV1CheckedLocalValueCore =
                  VVar (grammarV1ResolvedBinderCoreName resolvedBinder)
              }
            Left (GrammarV1BinderNotInScope _) -> Nothing
            Left _ -> Nothing
    _ -> Nothing
