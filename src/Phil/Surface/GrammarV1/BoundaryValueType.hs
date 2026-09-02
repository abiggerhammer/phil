module Phil.Surface.GrammarV1.BoundaryValueType
  ( grammarV1BoundaryValueType
  , grammarV1CheckedBoundaryValueType
  ) where

import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundType (grammarV1BoundType)
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedType)
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

-- | Route the same declared boundary value type through the uniform checked
-- Grammar-v1 type dispatcher. Ordinary structurally supported types retain their
-- exact Core Ty with an empty focusing trace. Proof/refinement types retain Core
-- proposition focusing success or FocusingError without falling back to the
-- structural bridge. Unsupported source types remain Nothing. No boundary-local
-- claim semantics, coercion, evidence, mode rule, or fallback is introduced.
grammarV1CheckedBoundaryValueType
  :: StaticContext
  -> SurfaceState
  -> GrammarV1BoundaryDecl
  -> Maybe (Either FocusingError (Ty, [FocusStep]))
grammarV1CheckedBoundaryValueType staticContext state boundary =
  grammarV1CheckedType
    staticContext
    state
    (locatedValue (grammarV1BoundaryType boundary))
