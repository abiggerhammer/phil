module Phil.Surface.GrammarV1.FunctionBodySurface
  ( GrammarV1CheckedClosedFunctionBody (..)
  , GrammarV1FunctionBodySurfaceError (..)
  , grammarV1CheckedClosedFunctionBody
  ) where

import Phil.Core.Focusing (FocusingError)
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Control (..), Ty)
import Phil.Surface.Check.Engine (checkSurfaceComponent)
import Phil.Surface.Check.Types
  ( SurfaceCheckError
  , SurfaceCheckResult (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.GrammarV1.CallableSignature
  ( GrammarV1CheckedFunctionHeader (..)
  , grammarV1CheckedClosedFunctionHeader
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1Statement (..)
  )
import Phil.Surface.Syntax
  ( Block (..)
  , Component (..)
  , Located (..)
  , Statement (..)
  , SurfaceExpression (..)
  )

-- | Checked Grammar-v1 function-body carrier. The already-checked header is
-- retained unchanged and the body result is the ordinary production surface
-- checker's exact terminal-control projection.
data GrammarV1CheckedClosedFunctionBody = GrammarV1CheckedClosedFunctionBody
  { checkedClosedFunctionBodyHeader :: GrammarV1CheckedFunctionHeader
  , checkedClosedFunctionBodyControls :: [Control]
  }
  deriving (Eq, Show)

data GrammarV1FunctionBodySurfaceError
  = GrammarV1FunctionBodyHeaderFocusingError FocusingError
  | GrammarV1FunctionBodyHeaderMismatch
      GrammarV1CheckedFunctionHeader
      GrammarV1CheckedFunctionHeader
  | GrammarV1FunctionBodySurfaceCheckError SurfaceCheckError
  | GrammarV1FunctionBodyResultMismatch Ty [Control]
  deriving (Eq, Show)

-- | Route the bounded closed body-semantic fragment through the existing
-- production surface checker rather than introducing a second body checker.
--
-- This slice remains deliberately parameter-free so no source term spelling is
-- used as binder authority and SURF-009 stays separate. Every admitted statement
-- is either a return or an expression statement, and every admitted expression is
-- recursively limited to Bool/Unit and parentheses. Source order is preserved
-- exactly. The production checker therefore owns sequencing semantics, including
-- rejection of statements after terminal control and ordinary unrestricted-value
-- discard behavior.
--
-- The supplied checked header is re-derived from the same source declaration and
-- stable declaration/definition identities before body checking, preventing a
-- checked body from being attached to a different function header. The synthetic
-- surface component has no parameters or provides contract; its only purpose is
-- to reuse the established expression/control/resource checker. Success still
-- requires exact terminal control to be one Return of the header's already-checked
-- result type. Calls, names, literals other than Bool/Unit, let-bindings,
-- branching, protocol/resource operations, closures, and all other body forms
-- remain structural non-competence (Nothing).
grammarV1CheckedClosedFunctionBody
  :: StaticContext
  -> GrammarV1CheckedFunctionHeader
  -> GrammarV1FunctionDecl
  -> Maybe
      (Either
        GrammarV1FunctionBodySurfaceError
        GrammarV1CheckedClosedFunctionBody)
grammarV1CheckedClosedFunctionBody staticContext expectedHeader source = do
  rechecked <- grammarV1CheckedClosedFunctionHeader
    staticContext
    (checkedFunctionDeclarationKey expectedHeader)
    (checkedFunctionDefinitionRevision expectedHeader)
    source
  case rechecked of
    Left focusingError ->
      pure (Left (GrammarV1FunctionBodyHeaderFocusingError focusingError))
    Right (actualHeader, _)
      | actualHeader /= expectedHeader ->
          pure (Left (GrammarV1FunctionBodyHeaderMismatch expectedHeader actualHeader))
      | not (null (checkedFunctionParameters actualHeader)) -> Nothing
      | otherwise -> do
          body <- grammarV1ClosedBody (grammarV1FunctionBody source)
          let syntheticComponent = Located
                (locatedSpan (grammarV1FunctionBody source))
                (Component
                  { componentName = checkedFunctionDisplayName actualHeader
                  , componentParameters = []
                  , componentProvides = Nothing
                  , componentBody = body
                  })
          pure $ do
            checked <- mapLeft GrammarV1FunctionBodySurfaceCheckError $
              checkSurfaceComponent
                (emptySurfaceEnvironment staticContext)
                syntheticComponent
            let controls = checkedTerminalControls checked
                expectedResult = checkedFunctionResultType actualHeader
            if controls == [Return expectedResult]
              then Right GrammarV1CheckedClosedFunctionBody
                { checkedClosedFunctionBodyHeader = actualHeader
                , checkedClosedFunctionBodyControls = controls
                }
              else Left (GrammarV1FunctionBodyResultMismatch expectedResult controls)

grammarV1ClosedBody :: Located GrammarV1Block -> Maybe (Located Block)
grammarV1ClosedBody (Located blockSpan (GrammarV1Block statements)) = do
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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
