module Phil.Surface.GrammarV1.IntrinsicRefinementType
  ( grammarV1IntrinsicRefinementType
  ) where

import Phil.Core.Syntax (Name (..), Ty (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.IntrinsicProposition
  ( grammarV1IntrinsicProposition
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))
import Phil.Surface.Syntax (Located (..))

-- | Preserve the first context-free Grammar-v1 refinement-type fragment exactly.
-- The binder identity is retained even though this bounded slice does not yet
-- place that binder in scope while elaborating the predicate. The base must be
-- one already-verified primitive type, and the predicate must belong wholly to
-- the already-verified intrinsic proposition fragment. A predicate that mentions
-- the refinement binder, or any other contextual/specialized form, therefore
-- fails closed for the later binder-scoped refinement bridge rather than gaining
-- an invented binding or lookup rule.
grammarV1IntrinsicRefinementType :: GrammarV1Type -> Maybe Ty
grammarV1IntrinsicRefinementType sourceType = case sourceType of
  GrammarV1RefinementType binder baseType proposition -> do
    base <- grammarV1PrimitiveType (locatedValue baseType)
    predicate <- grammarV1IntrinsicProposition (locatedValue proposition)
    Just (TyRefined (Name (locatedValue binder)) base predicate)
  _ -> Nothing
