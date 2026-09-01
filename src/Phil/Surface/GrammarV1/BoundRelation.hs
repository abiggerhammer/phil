module Phil.Surface.GrammarV1.BoundRelation
  ( grammarV1BoundRelationProposition
  ) where

import Control.Applicative ((<|>))
import Phil.Core.SortCheck (checkPropositionSorts)
import Phil.Core.Syntax (Proposition, RefTerm)
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.BoundRef (grammarV1BoundRefTerm)
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1IntrinsicRefLiteral
  , grammarV1RelationProposition
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Proposition (..))
import Phil.Surface.Syntax (Located (..))

-- | Compose only relation operands whose reference-term meaning is already
-- verified: intrinsic scalar literals or simple live surface bindings. The
-- parser-selected relation operator is preserved exactly, then the existing Core
-- proposition sort checker must accept the complete relation. Unknown/consumed
-- names, richer source expressions, sort mismatches, and invalid ordered sorts
-- therefore remain fail-closed rather than acquiring an invented interpretation.
grammarV1BoundRelationProposition
  :: SurfaceState
  -> GrammarV1Proposition
  -> Maybe Proposition
grammarV1BoundRelationProposition state source = case source of
  GrammarV1RelationProposition left operator right -> do
    leftTerm <- verifiedTerm left
    rightTerm <- verifiedTerm right
    let proposition = grammarV1RelationProposition
          (locatedValue operator)
          leftTerm
          rightTerm
    case checkPropositionSorts (stateCore state) proposition of
      Right () -> Just proposition
      Left _ -> Nothing
  _ -> Nothing
  where
    verifiedTerm :: Located a -> Maybe RefTerm
    verifiedTerm = error "unreachable"
