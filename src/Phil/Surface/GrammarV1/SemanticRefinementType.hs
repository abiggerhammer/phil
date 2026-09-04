module Phil.Surface.GrammarV1.SemanticRefinementType
  ( GrammarV1CheckedSemanticRefinementType (..)
  , GrammarV1SemanticRefinementTypeError (..)
  , grammarV1CheckedSemanticRefinementType
  ) where

import qualified Data.Set as Set
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceCheckError
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (GrammarV1RefinementBinder)
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1BindLocal
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  )
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedPropositionReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Proposition
  , GrammarV1Type (..)
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  , grammarV1RewritePropositionReferences
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact semantic result for the primitive-base refinement fragment. The binder
-- remains attached for diagnostics/identity evidence, while the Core refinement
-- and predicate use its generated semantic Name. The post-refinement lexical
-- scope is returned separately by the checker so callers can continue the same
-- declaration-wide ordinal stream after the child scope closes.
data GrammarV1CheckedSemanticRefinementType =
  GrammarV1CheckedSemanticRefinementType
    { checkedSemanticRefinementBinder :: GrammarV1ResolvedBinder
    , checkedSemanticRefinementReferences :: [GrammarV1CheckedLexicalReference]
    , checkedSemanticRefinementType :: Ty
    , checkedSemanticRefinementFocusSteps :: [FocusStep]
    }
  deriving (Eq, Show)

-- | Failures on the semantic refinement path remain separated by authority. A
-- primitive refinement is admitted structurally before lexical-reference,
-- rewrite, SurfaceState insertion, and Core focusing failures become explicit.
data GrammarV1SemanticRefinementTypeError
  = GrammarV1SemanticRefinementBinderScopeError GrammarV1BinderScopeError
  | GrammarV1SemanticRefinementReferenceNonCompetent
      (Located GrammarV1Proposition)
  | GrammarV1SemanticRefinementReferenceError
      GrammarV1LexicalReferenceError
  | GrammarV1SemanticRefinementRewriteNonCompetent
      (Located GrammarV1Proposition)
  | GrammarV1SemanticRefinementBindingError
      GrammarV1ResolvedBinder
      SurfaceCheckError
  | GrammarV1SemanticRefinementCheckNonCompetent
      (Located GrammarV1Proposition)
  | GrammarV1SemanticRefinementFocusingError
      FocusingError
  deriving (Eq, Show)

-- | Check one primitive-base refinement using the caller's exact lexical scope.
-- The refinement binder lives in a child frame only for its predicate, but its
-- fresh ordinal is retained after that frame closes. This prevents nested/sibling
-- refinement binders from minting a private identity stream and lets active outer
-- term binders participate in the ordinary no-shadowing rule.
--
-- SurfaceState is only a semantic carrier here: the binder is inserted under the
-- resolver-issued Core Name, never under source spelling. Predicate occurrences
-- are rewritten only where LexicalReferenceScope certified an exact local use.
grammarV1CheckedSemanticRefinementType
  :: StaticContext
  -> GrammarV1LexicalScope
  -> SurfaceState
  -> GrammarV1Type
  -> Maybe
      (Either
        GrammarV1SemanticRefinementTypeError
        (GrammarV1CheckedSemanticRefinementType, GrammarV1LexicalScope))
grammarV1CheckedSemanticRefinementType staticContext outerScope state sourceType =
  case sourceType of
    GrammarV1RefinementType sourceBinder baseType proposition -> do
      base <- grammarV1PrimitiveType (locatedValue baseType)
      let childScope = grammarV1EnterLexicalScope outerScope
      pure $ case grammarV1BindLocal
          GrammarV1RefinementBinder
          sourceBinder
          childScope of
        Left scopeError ->
          Left (GrammarV1SemanticRefinementBinderScopeError scopeError)
        Right (binder, boundScope) -> do
          references <- case grammarV1CheckedPropositionReferences
              Set.empty
              boundScope
              proposition of
            Nothing -> Left
              (GrammarV1SemanticRefinementReferenceNonCompetent proposition)
            Just (Left referenceError) -> Left
              (GrammarV1SemanticRefinementReferenceError referenceError)
            Just (Right checkedReferences) -> Right checkedReferences
          rewritten <- maybe
            (Left (GrammarV1SemanticRefinementRewriteNonCompetent proposition))
            Right
            (grammarV1RewritePropositionReferences references proposition)
          scopedState <- mapLeft
            (GrammarV1SemanticRefinementBindingError binder)
            ( grammarV1InsertSemanticBinding
                binder
                (BindingMeta Unrestricted base PlainShape)
                state
            )
          checked <- case grammarV1CheckedProposition
              staticContext
              scopedState
              (locatedValue rewritten) of
            Nothing -> Left
              (GrammarV1SemanticRefinementCheckNonCompetent rewritten)
            Just (Left focusingError) -> Left
              (GrammarV1SemanticRefinementFocusingError focusingError)
            Just (Right result) -> Right result
          nextOuterScope <- mapLeft
            GrammarV1SemanticRefinementBinderScopeError
            (grammarV1LeaveLexicalScope boundScope)
          let (predicate, steps) = checked
          Right
            ( GrammarV1CheckedSemanticRefinementType
                { checkedSemanticRefinementBinder = binder
                , checkedSemanticRefinementReferences = references
                , checkedSemanticRefinementType =
                    TyRefined
                      (grammarV1ResolvedBinderCoreName binder)
                      base
                      predicate
                , checkedSemanticRefinementFocusSteps = steps
                }
            , nextOuterScope
            )
    _ -> Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
