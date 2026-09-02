module Phil.Surface.GrammarV1.BoundRefinementType
  ( grammarV1BoundRefinementType
  ) where

import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Support (insertBindingMeta)
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser (GrammarV1Type (..))
import Phil.Surface.Syntax (Located (..))

-- | Elaborate primitive-base Grammar-v1 refinements with the declared binder
-- available only while checking the predicate. Primitive types already have the
-- established unrestricted surface mode, so this temporary logical binding does
-- not choose a new general type-to-mode rule. The extended SurfaceState is never
-- returned: it exists only to give the verified binding-aware proposition bridge
-- the exact binder sort and lexical visibility required by the refinement body.
-- Existing active names still reject through insertBindingMeta rather than being
-- silently shadowed, and every unsupported predicate/base form remains fail-closed.
grammarV1BoundRefinementType
  :: SurfaceState
  -> GrammarV1Type
  -> Maybe Ty
grammarV1BoundRefinementType state sourceType = case sourceType of
  GrammarV1RefinementType binder baseType proposition -> do
    base <- grammarV1PrimitiveType (locatedValue baseType)
    let binderText = locatedValue binder
    scopedState <- either (const Nothing) Just $
      insertBindingMeta
        (locatedSpan binder)
        binderText
        (BindingMeta Unrestricted base PlainShape)
        state
    predicate <- grammarV1BoundProposition scopedState (locatedValue proposition)
    Just (TyRefined (Name binderText) base predicate)
  _ -> Nothing
