module Phil.Surface.GrammarV1.BoundProofType
  ( grammarV1BoundProofType
  ) where

import Phil.Core.Syntax (Ty (..))
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))
import Phil.Surface.Syntax (Located (..))

-- | Elaborate a Proof[...] type exactly when its entire proposition already has
-- verified binding-aware meaning. The proposition payload delegates only to the
-- #506 bridge, so live simple references may participate through the verified
-- relation and claim leaves while intrinsic truth leaves remain unchanged.
-- Any unknown, consumed, specialized, projected, arithmetic, or otherwise
-- unresolved nested leaf makes the whole Proof type fail closed; this bridge
-- invents no evidence, binding, coercion, claim identity, sort rule, or proof.
grammarV1BoundProofType
  :: SurfaceState
  -> GrammarV1Type
  -> Maybe Ty
grammarV1BoundProofType state sourceType = case sourceType of
  GrammarV1ProofType (Located _ proposition) ->
    TyProof <$> grammarV1BoundProposition state proposition
  _ -> Nothing
