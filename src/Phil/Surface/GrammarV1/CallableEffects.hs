module Phil.Surface.GrammarV1.CallableEffects
  ( grammarV1SemanticEffect
  , grammarV1EffectSet
  , grammarV1CallableEffectBounds
  ) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1EffectExpression (..)
  , GrammarV1EffectSetExpression (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve the first exact Grammar-v1 effect identity fragment as Core's
-- Text-backed SemanticEffect. Only argument-free, unspecialized static
-- references are competent here; term arguments and static specialization carry
-- additional semantics and therefore remain unresolved rather than being
-- flattened into a string.
grammarV1SemanticEffect
  :: GrammarV1EffectExpression
  -> Maybe SemanticEffect
grammarV1SemanticEffect effect
  | not (null (grammarV1EffectArguments effect)) = Nothing
  | not (null (grammarV1StaticReferenceArguments reference)) = Nothing
  | otherwise = case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
      [] -> Nothing
      parts -> Just (SemanticEffect (Text.intercalate (Text.singleton '.') parts))
  where
    reference = locatedValue (grammarV1EffectReference effect)

-- | Route a literal Grammar-v1 effect set into Core's finite SemanticEffect set.
-- Literal ordering and duplicate spelling are intentionally normalized by the
-- semantic Set carrier. Effect-set references remain unresolved until the
-- expected static Effects parameter is competently resolved.
grammarV1EffectSet
  :: GrammarV1EffectSetExpression
  -> Maybe (Set.Set SemanticEffect)
grammarV1EffectSet source = case source of
  GrammarV1EffectSetLiteral effects ->
    Set.fromList <$> mapM
      (grammarV1SemanticEffect . locatedValue)
      effects
  GrammarV1EffectSetReference _ -> Nothing

-- | Preserve each callable effects clause as a separate Core effect bound in
-- source order. This projection does not invent a declaration-level cardinality
-- rule or silently union multiple clauses; callers retain that distinction.
-- Exact absence is Just []. One unresolved effect set rejects the projection in
-- full rather than dropping or partially accepting it.
grammarV1CallableEffectBounds
  :: GrammarV1CallableContractDecl
  -> Maybe [Set.Set SemanticEffect]
grammarV1CallableEffectBounds source =
  mapM elaborate
    [ effectSet
    | Located _ (GrammarV1CallableEffects effectSet) <- grammarV1CallableClauses source
    ]
  where
    elaborate (Located _ effectSet) = grammarV1EffectSet effectSet
