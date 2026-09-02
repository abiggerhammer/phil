module Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  ) where

import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundType
  ( grammarV1BoundType
  )
import Phil.Surface.GrammarV1.CheckedProofType
  ( grammarV1CheckedProofType
  )
import Phil.Surface.GrammarV1.CheckedRefinementType
  ( grammarV1CheckedRefinementType
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Type (..)
  )

-- | Provide one checked entry point for every currently supported Grammar-v1
-- type fragment. Proof and refinement types retain the checked proposition
-- semantics established by their dedicated bridges, including Core focusing
-- errors and traces. Every other already-supported type delegates once to the
-- existing binding-aware structural dispatcher and carries an empty focusing
-- trace because no proposition focusing occurred. Structural source
-- non-competence remains Nothing throughout; this dispatcher invents no type
-- interpretation, claim semantics, coercion, evidence, element mode, or fallback.
grammarV1CheckedType
  :: StaticContext
  -> SurfaceState
  -> GrammarV1Type
  -> Maybe (Either FocusingError (Ty, [FocusStep]))
grammarV1CheckedType staticContext state sourceType =
  case sourceType of
    GrammarV1ProofType _ ->
      grammarV1CheckedProofType staticContext state sourceType
    GrammarV1RefinementType _ _ _ ->
      grammarV1CheckedRefinementType staticContext state sourceType
    _ -> do
      ty <- grammarV1BoundType state sourceType
      pure (Right (ty, []))
