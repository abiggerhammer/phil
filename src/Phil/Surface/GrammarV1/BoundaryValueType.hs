module Phil.Surface.GrammarV1.BoundaryValueType
  ( grammarV1BoundaryValueType
  ) where

import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundType (grammarV1BoundType)
import Phil.Surface.GrammarV1.Parser (GrammarV1BoundaryDecl (..))
import Phil.Surface.Syntax (Located (..))

-- | Route the declared semantic value type of one Grammar-v1 boundary through
-- the already-verified binding-aware type dispatcher. This bridge contributes
-- no boundary-local type interpretation: every supported type retains its
-- existing Core meaning, while tuple modes, unresolved specialization, and
-- every other type form outside grammarV1BoundType remain fail-closed.
grammarV1BoundaryValueType
  :: SurfaceState
  -> GrammarV1BoundaryDecl
  -> Maybe Ty
grammarV1BoundaryValueType state boundary =
  grammarV1BoundType state (locatedValue (grammarV1BoundaryType boundary))
