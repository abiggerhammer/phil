module Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
  ) where

import Phil.Core.Syntax (Proposition (..))
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundClaimApplication
  ( grammarV1BoundClaimApplication
  )
import Phil.Surface.GrammarV1.BoundRelation
  ( grammarV1BoundRelationProposition
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Proposition (..))
import Phil.Surface.Syntax (Located (..))

-- | Compose only proposition fragments whose leaves already have verified
-- binding-aware meaning. Truth literals remain intrinsic; relation leaves
-- delegate to the #501 bridge and claim applications to the #505 bridge.
-- Any unknown, consumed, specialized, projected, arithmetic, or otherwise
-- unresolved nested leaf therefore fails the whole logical tree closed rather
-- than producing a partial proposition or falling back to another meaning.
grammarV1BoundProposition
  :: SurfaceState
  -> GrammarV1Proposition
  -> Maybe Proposition
grammarV1BoundProposition state source = case source of
  GrammarV1TrueProposition -> Just Truth
  GrammarV1FalseProposition -> Just Falsehood
  GrammarV1RelationProposition _ _ _ ->
    grammarV1BoundRelationProposition state source
  GrammarV1ClaimApplicationProposition _ _ ->
    grammarV1BoundClaimApplication state source
  GrammarV1NotProposition (Located _ inner) ->
    Negation <$> grammarV1BoundProposition state inner
  GrammarV1AndProposition (Located _ left) (Located _ right) ->
    Conjunction
      <$> grammarV1BoundProposition state left
      <*> grammarV1BoundProposition state right
  GrammarV1OrProposition (Located _ left) (Located _ right) ->
    Disjunction
      <$> grammarV1BoundProposition state left
      <*> grammarV1BoundProposition state right
