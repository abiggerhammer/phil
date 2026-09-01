module Phil.Surface.GrammarV1.BoundType
  ( grammarV1BoundType
  ) where

import Control.Applicative ((<|>))
import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundBytesType
  ( grammarV1BoundBytesType
  )
import Phil.Surface.GrammarV1.BoundProofType
  ( grammarV1BoundProofType
  )
import Phil.Surface.GrammarV1.IntrinsicType
  ( grammarV1IntrinsicType
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))

-- | Compose only type fragments whose source-to-Core meaning is already
-- verified. Context-free types continue through the #496 dispatcher; Bytes
-- additionally admits the #499 live Nat-bound form, and Proof delegates to the
-- #509 binding-aware proposition composition. The two Bytes routes are the
-- already-verified literal and live-simple-name fragments; failure in both
-- remains failure rather than triggering any new interpretation. All richer
-- contextual type forms remain unresolved.
grammarV1BoundType
  :: SurfaceState
  -> GrammarV1Type
  -> Maybe Ty
grammarV1BoundType state sourceType = case sourceType of
  GrammarV1BytesType _ ->
    grammarV1IntrinsicType sourceType
      <|> grammarV1BoundBytesType state sourceType
  GrammarV1ProofType _ -> grammarV1BoundProofType state sourceType
  _ -> grammarV1IntrinsicType sourceType
