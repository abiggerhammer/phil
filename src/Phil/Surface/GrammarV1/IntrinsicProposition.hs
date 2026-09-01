module Phil.Surface.GrammarV1.IntrinsicProposition
  ( grammarV1IntrinsicProposition
  ) where

import Phil.Core.Syntax (Proposition (..))
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1IntrinsicClaimApplication
  , grammarV1IntrinsicRelationProposition
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Proposition (..))
import Phil.Surface.Syntax (Located (..))

-- | Compose only proposition fragments whose source-to-Core leaves already have
-- context-free verified elaboration. Any contextual relation operand, specialized
-- claim reference, bound claim argument, or other unresolved leaf causes the
-- entire surrounding logical tree to fail closed rather than producing a partial
-- proposition or falling back to another interpretation.
grammarV1IntrinsicProposition :: GrammarV1Proposition -> Maybe Proposition
grammarV1IntrinsicProposition source = case source of
  GrammarV1TrueProposition -> Just Truth
  GrammarV1FalseProposition -> Just Falsehood
  GrammarV1RelationProposition _ _ _ ->
    grammarV1IntrinsicRelationProposition source
  GrammarV1ClaimApplicationProposition _ _ ->
    grammarV1IntrinsicClaimApplication source
  GrammarV1NotProposition (Located _ inner) ->
    Negation <$> grammarV1IntrinsicProposition inner
  GrammarV1AndProposition (Located _ left) (Located _ right) ->
    Conjunction
      <$> grammarV1IntrinsicProposition left
      <*> grammarV1IntrinsicProposition right
  GrammarV1OrProposition (Located _ left) (Located _ right) ->
    Disjunction
      <$> grammarV1IntrinsicProposition left
      <*> grammarV1IntrinsicProposition right
