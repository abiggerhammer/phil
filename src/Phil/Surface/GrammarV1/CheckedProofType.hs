module Phil.Surface.GrammarV1.CheckedProofType
  ( grammarV1CheckedProofType
  ) where

import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))
import Phil.Surface.Syntax (Located (..))

-- | Route a structurally supported Grammar-v1 Proof[...] type through the
-- already checked whole-proposition bridge before constructing TyProof. Source
-- non-competence remains Nothing. Core semantic rejection remains Just (Left
-- ...). Only a proposition accepted and canonicalized by Core focusing becomes
-- TyProof, with the exact focusing trace preserved for callers. This bridge
-- invents no claim meaning, coercion, evidence, proof object, or fallback.
grammarV1CheckedProofType
  :: StaticContext
  -> SurfaceState
  -> GrammarV1Type
  -> Maybe (Either FocusingError (Ty, [FocusStep]))
grammarV1CheckedProofType staticContext state sourceType =
  case sourceType of
    GrammarV1ProofType (Located _ proposition) -> do
      checked <- grammarV1CheckedProposition staticContext state proposition
      pure $ fmap
        (\(canonical, steps) -> (TyProof canonical, steps))
        checked
    _ -> Nothing
