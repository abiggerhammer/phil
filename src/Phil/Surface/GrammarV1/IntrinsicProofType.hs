module Phil.Surface.GrammarV1.IntrinsicProofType
  ( grammarV1IntrinsicProofType
  ) where

import Phil.Core.Syntax (Ty (..))
import Phil.Surface.GrammarV1.IntrinsicProposition
  ( grammarV1IntrinsicProposition
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))
import Phil.Surface.Syntax (Located (..))

-- | Elaborate a Proof[...] type exactly when its entire proposition belongs to
-- the verified context-free proposition fragment. This adds no new leaf meaning:
-- truth values, literal relations, unspecialized literal-argument claims, and
-- not/and/or composition are delegated to grammarV1IntrinsicProposition. Any
-- contextual or specialized nested leaf therefore makes the whole Proof type
-- fail closed rather than acquiring invented evidence, identity, or bindings.
grammarV1IntrinsicProofType :: GrammarV1Type -> Maybe Ty
grammarV1IntrinsicProofType sourceType = case sourceType of
  GrammarV1ProofType (Located _ proposition) ->
    TyProof <$> grammarV1IntrinsicProposition proposition
  _ -> Nothing
