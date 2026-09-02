module Phil.Surface.GrammarV1.BoundaryFailureTypes
  ( grammarV1BoundaryFailureTypes
  ) where

import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundType (grammarV1BoundType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BoundaryDecl (..)
  , GrammarV1BoundaryItem (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve every declared boundary failure type in source order and delegate
-- each type exactly once to the verified binding-aware type dispatcher. Exact
-- absence is represented by the empty list. If any declared failure type is
-- outside current type competence, the whole declaration-level bridge fails
-- closed rather than dropping or partially accepting that failure surface.
grammarV1BoundaryFailureTypes
  :: SurfaceState
  -> GrammarV1BoundaryDecl
  -> Maybe [Ty]
grammarV1BoundaryFailureTypes state boundary =
  mapM elaborateFailure failureTypes
  where
    failureTypes =
      [ failureType
      | Located _ item <- grammarV1BoundaryItems boundary
      , GrammarV1BoundaryFailure failureType <- [item]
      ]

    elaborateFailure (Located _ sourceType) =
      grammarV1BoundType state sourceType
