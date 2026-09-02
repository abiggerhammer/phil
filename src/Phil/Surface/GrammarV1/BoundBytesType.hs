module Phil.Surface.GrammarV1.BoundBytesType
  ( grammarV1BoundBytesType
  ) where

import Phil.Core.SortCheck (sortOfRefTerm)
import Phil.Core.Syntax (RefSort (..), Ty (..))
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.BoundRefExpression
  ( grammarV1BoundRefExpression
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))

-- | Compose the verified binding-aware refinement-expression bridge with the
-- competent Core sort checker for Grammar-v1 Bytes[...] sizes. Any expression
-- already preserved by that bridge may become a TyBytes index only when its
-- exact Core term has Nat sort in the existing resource/check state. This
-- therefore admits intrinsic Nat literals, live Nat names, parentheses, Nat
-- add/sub, literal scaling, len, and explicit toNat without inventing a
-- Bytes-local expression language. Raw UInt/Bool terms, symbolic multiplication,
-- projection, unknown/consumed names, and every other unresolved source form
-- remain fail-closed. Subtraction side conditions remain a later focusing/
-- obligation concern rather than being erased or discharged here.
grammarV1BoundBytesType :: SurfaceState -> GrammarV1Type -> Maybe Ty
grammarV1BoundBytesType state sourceType = case sourceType of
  GrammarV1BytesType sizeExpression -> do
    size <- grammarV1BoundRefExpression state sizeExpression
    case sortOfRefTerm (stateCore state) size of
      Right SortNat -> Just (TyBytes size)
      _ -> Nothing
  _ -> Nothing
