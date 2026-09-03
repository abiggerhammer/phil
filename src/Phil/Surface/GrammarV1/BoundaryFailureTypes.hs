module Phil.Surface.GrammarV1.BoundaryFailureTypes
  ( grammarV1BoundaryFailureTypes
  , grammarV1CheckedBoundaryFailureTypes
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
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BoundaryDecl (..)
  , GrammarV1BoundaryItem (..)
  , GrammarV1Type
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
  mapM elaborateFailure (boundaryFailureTypes boundary)
  where
    elaborateFailure (Located _ sourceType) =
      grammarV1BoundType state sourceType

-- | Route the same ordered boundary failure surface through the uniform checked
-- type dispatcher. Structurally supported ordinary types retain their exact Ty
-- and an empty focusing trace; checked Proof/refinement types preserve Core
-- canonicalization and FocusStep evidence. The first Core semantic rejection is
-- retained as Left in source order, while any structurally non-competent failure
-- type rejects the entire projection as Nothing. Exact absence is Just (Right []).
grammarV1CheckedBoundaryFailureTypes
  :: StaticContext
  -> SurfaceState
  -> GrammarV1BoundaryDecl
  -> Maybe (Either FocusingError [(Ty, [FocusStep])])
grammarV1CheckedBoundaryFailureTypes staticContext state boundary = do
  checked <- mapM
    (\(Located _ sourceType) ->
      grammarV1CheckedType staticContext state sourceType)
    (boundaryFailureTypes boundary)
  pure (sequence checked)

boundaryFailureTypes
  :: GrammarV1BoundaryDecl
  -> [Located GrammarV1Type]
boundaryFailureTypes boundary =
  [ failureType
  | Located _ item <- grammarV1BoundaryItems boundary
  , GrammarV1BoundaryFailure failureType <- [item]
  ]
