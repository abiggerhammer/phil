module Phil.Core.CallableSemanticContract
  ( SourceCallableSemanticContract (..)
  ) where

import Phil.Core.CallableOutcome (CallableOutcomeContract)
import Phil.Core.CallableRefinement (CallableRefinementSurface)

-- | Complete already-checked semantic surface attached to one ordinary source
-- callable. The bounded refinement surface owns machine shape, caller authority,
-- public may-effects, modeled failures, and the global callee transition. The
-- outcome contracts retain branch-sensitive state, callee transition,
-- postconditions, residual obligations, assumptions, effects, and discharged
-- facts. Keeping the two authorities in one neutral Core value lets compiler
-- resolution and surface invocation share the exact same semantic object without
-- introducing a Surface <-> Compiler dependency cycle.
data SourceCallableSemanticContract = SourceCallableSemanticContract
  { sourceCallableRefinementSurface :: CallableRefinementSurface
  , sourceCallableOutcomeContracts :: [CallableOutcomeContract]
  }
  deriving (Eq, Ord, Show)
