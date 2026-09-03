module Phil.Surface.GrammarV1.ComponentBodySurface
  ( GrammarV1CheckedClosedComponentBody (..)
  , GrammarV1ComponentBodySurfaceError (..)
  , grammarV1CheckedClosedComponentBody
  ) where

import Phil.Core.Focusing (FocusingError)
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Control)
import Phil.Surface.Check.Engine (checkSurfaceComponent)
import Phil.Surface.Check.Types
  ( SurfaceCheckError
  , SurfaceCheckResult (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.GrammarV1.ClosedBodySurface
  ( grammarV1ClosedBoolUnitBlock
  )
import Phil.Surface.GrammarV1.ComponentSurface
  ( GrammarV1CheckedComponentHeader (..)
  , grammarV1CheckedClosedComponentHeader
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ComponentDecl (..)
  )
import Phil.Surface.Syntax
  ( Component (..)
  , Located (..)
  )

-- | First checked Grammar-v1 component-body carrier. The checked declaration
-- header remains attached unchanged and production surface checking owns the
-- body's exact terminal-control projection.
data GrammarV1CheckedClosedComponentBody = GrammarV1CheckedClosedComponentBody
  { checkedClosedComponentBodyHeader :: GrammarV1CheckedComponentHeader
  , checkedClosedComponentBodyControls :: [Control]
  }
  deriving (Eq, Show)

data GrammarV1ComponentBodySurfaceError
  = GrammarV1ComponentBodyHeaderFocusingError FocusingError
  | GrammarV1ComponentBodyHeaderMismatch
      GrammarV1CheckedComponentHeader
      GrammarV1CheckedComponentHeader
  | GrammarV1ComponentBodySurfaceCheckError SurfaceCheckError
  deriving (Eq, Show)

-- | Route the same bounded binder-free Bool/Unit statement fragment used by
-- closed function bodies through the existing production component checker.
--
-- The supplied checked header is re-derived from the same source declaration and
-- stable DeclarationKey/DefinitionRevision before body checking. Omitted and
-- explicitly empty parameter lists remain admissible; any live term parameter is
-- outside this SURF-008 body slice so SURF-009 binder identity/scope stays
-- separate. A source `provides` type is rechecked and retained on the header, but
-- the synthetic production-checking component deliberately carries no provides
-- syntax or expected architecture contract: this slice checks body semantics only
-- and does not claim architecture-contract satisfaction.
--
-- The shared closed-body bridge preserves source order and accepts only Bool/Unit
-- return/expression statements. Names, calls, integers, let-bindings, branching,
-- protocol/resource operations, closures and richer forms remain structural
-- non-competence. Production checking owns discard, control and resource
-- rejection; success records the exact terminal controls without inventing a
-- callable-style result contract for components.
grammarV1CheckedClosedComponentBody
  :: StaticContext
  -> GrammarV1CheckedComponentHeader
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1ComponentBodySurfaceError
        GrammarV1CheckedClosedComponentBody)
grammarV1CheckedClosedComponentBody staticContext expectedHeader source = do
  rechecked <- grammarV1CheckedClosedComponentHeader
    staticContext
    (checkedComponentDeclarationKey expectedHeader)
    (checkedComponentDefinitionRevision expectedHeader)
    source
  case rechecked of
    Left focusingError ->
      pure (Left (GrammarV1ComponentBodyHeaderFocusingError focusingError))
    Right (actualHeader, _)
      | actualHeader /= expectedHeader ->
          pure (Left (GrammarV1ComponentBodyHeaderMismatch expectedHeader actualHeader))
      | hasLiveParameters actualHeader -> Nothing
      | otherwise -> do
          body <- grammarV1ClosedBoolUnitBlock (grammarV1ComponentBody source)
          let syntheticComponent = Located
                (locatedSpan (grammarV1ComponentBody source))
                (Component
                  { componentName = checkedComponentDisplayName actualHeader
                  , componentParameters = []
                  , componentProvides = Nothing
                  , componentBody = body
                  })
          pure $ do
            checked <- mapLeft GrammarV1ComponentBodySurfaceCheckError $
              checkSurfaceComponent
                (emptySurfaceEnvironment staticContext)
                syntheticComponent
            Right GrammarV1CheckedClosedComponentBody
              { checkedClosedComponentBodyHeader = actualHeader
              , checkedClosedComponentBodyControls = checkedTerminalControls checked
              }

hasLiveParameters :: GrammarV1CheckedComponentHeader -> Bool
hasLiveParameters header = case checkedComponentParameters header of
  Nothing -> False
  Just parameters -> not (null parameters)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
