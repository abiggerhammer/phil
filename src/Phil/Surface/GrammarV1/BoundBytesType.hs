module Phil.Surface.GrammarV1.BoundBytesType
  ( grammarV1BoundBytesType
  ) where

import Phil.Core.SortCheck (sortOfRefTerm)
import Phil.Core.Syntax (RefSort (..), Ty (..))
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.BoundRef (grammarV1BoundRefTerm)
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))

-- | Compose the live-name bridge with the competent Core sort checker only for
-- Grammar-v1 Bytes[...] sizes. A live simple name must already have Nat sort in
-- the existing resource/check state before it can become a TyBytes index. Wrong
-- sorts and every source form rejected by grammarV1BoundRefTerm remain fail-closed.
grammarV1BoundBytesType :: SurfaceState -> GrammarV1Type -> Maybe Ty
grammarV1BoundBytesType state sourceType = case sourceType of
  GrammarV1BytesType sizeExpression -> do
    size <- grammarV1BoundRefTerm state sizeExpression
    case sortOfRefTerm (stateCore state) size of
      Right SortNat -> Just (TyBytes size)
      _ -> Nothing
  _ -> Nothing
