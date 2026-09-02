module Phil.Surface.GrammarV1.BoundRelation
  ( grammarV1BoundRelationProposition
  ) where

import Phil.Core.SortCheck (checkPropositionSorts)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.BoundRefExpression
  ( grammarV1BoundRefExpression
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1RelationProposition
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Proposition (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Compose relation operands through the verified binding-aware Phase-1
-- refinement-expression bridge, preserve the parser-selected relation operator
-- exactly, then require the existing Core sort checker to accept the completed
-- proposition. This admits already-structural Nat arithmetic, len, explicit
-- toNat, and literal scaling without inventing consumer-local expression rules.
-- Projection and unresolved names still fail in the expression bridge; mixed
-- UInt/Nat relations remain fail-closed here until the focusing/coercion boundary
-- is composed explicitly.
grammarV1BoundRelationProposition
  :: SurfaceState
  -> GrammarV1Proposition
  -> Maybe Proposition
grammarV1BoundRelationProposition state source = case source of
  GrammarV1RelationProposition left operator right -> do
    leftTerm <- grammarV1BoundRefExpression state left
    rightTerm <- grammarV1BoundRefExpression state right
    let proposition = grammarV1RelationProposition
          (locatedValue operator)
          leftTerm
          rightTerm
    case checkPropositionSorts (stateCore state) proposition of
      Right () -> Just proposition
      Left _ -> Nothing
  _ -> Nothing
