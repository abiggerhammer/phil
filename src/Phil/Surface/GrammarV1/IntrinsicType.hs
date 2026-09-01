module Phil.Surface.GrammarV1.IntrinsicType
  ( grammarV1IntrinsicType
  ) where

import Phil.Core.Syntax (Ty)
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1IntrinsicBytesType
  , grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.IntrinsicProofType
  ( grammarV1IntrinsicProofType
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))

-- | Compose only Grammar-v1 type forms whose source-to-Core meaning has already
-- been verified as context-free. Primitive Unit/Bool/U<n>, literal-sized Bytes,
-- and intrinsic Proof types delegate to their exact verified bridges. Frame,
-- Validated, refinement, tuple, named, and any other context-dependent type form
-- remains unresolved rather than acquiring invented identity, element modes,
-- bindings, evidence, or static-reference meaning.
grammarV1IntrinsicType :: GrammarV1Type -> Maybe Ty
grammarV1IntrinsicType sourceType = case sourceType of
  GrammarV1UnitType -> grammarV1PrimitiveType sourceType
  GrammarV1BoolType -> grammarV1PrimitiveType sourceType
  GrammarV1UnsignedType _ -> grammarV1PrimitiveType sourceType
  GrammarV1BytesType _ -> grammarV1IntrinsicBytesType sourceType
  GrammarV1ProofType _ -> grammarV1IntrinsicProofType sourceType
  _ -> Nothing
