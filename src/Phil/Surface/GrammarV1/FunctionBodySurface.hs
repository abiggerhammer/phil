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
import Phil.Surface.GrammarV1.ClosedBodySurface
  ( grammarV1ClosedBoolUnitBlock
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl (..)
  )
import Phil.Surface.Syntax
  ( Component (..)
  , Located (..)
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
-- used as binder authority and SURF-009 stays separate. The shared
-- grammarV1ClosedBoolUnitBlock bridge preserves source order and admits only
-- Bool/Unit return/expression statements. The production checker therefore owns
-- sequencing semantics, including rejection after terminal control and ordinary
-- unrestricted-value discard behavior.
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
          body <- grammarV1ClosedBoolUnitBlock (grammarV1FunctionBody source)
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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
