module Phil.Surface.GrammarV1.ClosedBodySurface
  ( grammarV1ClosedBoolUnitBlock
  ) where

import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1Expression (..)
  , GrammarV1Statement (..)
  )
import Phil.Surface.Syntax
  ( Block (..)
  , Located (..)
  , Statement (..)
  , SurfaceExpression (..)
  )

-- | Lossless bridge for the bounded binder-free body fragment currently shared
-- by function and component correspondence. Every admitted statement is either
-- a return or expression statement and every admitted expression is recursively
-- Bool/Unit/parentheses. Source spans and statement order are preserved exactly.
--
-- This helper performs no semantic checking: the established production surface
-- checker remains authoritative for sequencing, discard, control, resource and
-- result behavior. Names, calls, integer literals, let-bindings, branches,
-- protocol/resource operations, closures and richer forms remain non-competence.
grammarV1ClosedBoolUnitBlock :: Located GrammarV1Block -> Maybe (Located Block)
grammarV1ClosedBoolUnitBlock (Located blockSpan (GrammarV1Block statements)) = do
  checked <- mapM grammarV1ClosedStatement statements
  pure (Located blockSpan (Block checked))

grammarV1ClosedStatement
  :: Located GrammarV1Statement
  -> Maybe (Located Statement)
grammarV1ClosedStatement (Located statementSpan source) =
  case source of
    GrammarV1ReturnStatement sourceExpression -> do
      expression <- grammarV1ClosedExpression sourceExpression
      pure (Located statementSpan (ReturnStatement expression))
    GrammarV1ExpressionStatement sourceExpression -> do
      expression <- grammarV1ClosedExpression sourceExpression
      pure (Located statementSpan (ExpressionStatement expression))
    GrammarV1LetStatement {} -> Nothing

grammarV1ClosedExpression
  :: Located GrammarV1Expression
  -> Maybe (Located SurfaceExpression)
grammarV1ClosedExpression (Located expressionSpan source) =
  case source of
    GrammarV1BoolExpression value ->
      Just (Located expressionSpan (BooleanExpression value))
    GrammarV1UnitExpression ->
      Just (Located expressionSpan UnitExpression)
    GrammarV1ParenthesizedExpression inner -> do
      checked <- grammarV1ClosedExpression inner
      Just (Located expressionSpan (locatedValue checked))
    _ -> Nothing
