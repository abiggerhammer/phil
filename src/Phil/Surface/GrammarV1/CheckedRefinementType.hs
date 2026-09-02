module Phil.Surface.GrammarV1.CheckedRefinementType
  ( grammarV1CheckedRefinementType
  ) where

import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support (insertBindingMeta)
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Check the already-supported primitive-base Grammar-v1 refinement fragment
-- through the whole-proposition Core focusing seam. The refinement binder uses
-- the same temporary unrestricted lexical scope as the established structural
-- bridge: primitive bases are the only admitted bases, and insertBindingMeta is
-- the sole scope/resource-context authority. Source non-competence remains
-- Nothing; once the complete predicate has structural meaning, Core semantic
-- rejection remains a distinct Left. Only a Core-accepted canonical predicate
-- becomes TyRefined, and the exact focusing trace is preserved. This bridge
-- invents no general type-to-mode rule, claim semantics, coercion, evidence,
-- shadowing policy, or fallback interpretation.
grammarV1CheckedRefinementType
  :: StaticContext
  -> SurfaceState
  -> GrammarV1Type
  -> Maybe (Either FocusingError (Ty, [FocusStep]))
grammarV1CheckedRefinementType staticContext state sourceType =
  case sourceType of
    GrammarV1RefinementType binder baseType proposition -> do
      base <- grammarV1PrimitiveType (locatedValue baseType)
      let binderText = locatedValue binder
      scopedState <- either (const Nothing) Just $
        insertBindingMeta
          (locatedSpan binder)
          binderText
          (BindingMeta Unrestricted base PlainShape)
          state
      checked <- grammarV1CheckedProposition
        staticContext
        scopedState
        (locatedValue proposition)
      pure $ do
        (predicate, steps) <- checked
        Right
          ( TyRefined (Name binderText) base predicate
          , steps
          )
    _ -> Nothing
