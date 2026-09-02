module Phil.Surface.GrammarV1.BoundRelation
  ( grammarV1BoundRelationProposition
  ) where

import Phil.Core.Focusing (canonicalizeProposition)
import Phil.Core.SortCheck (checkPropositionSorts)
import Phil.Core.Static (emptyStaticContext)
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
-- refinement-expression bridge and preserve the parser-selected relation
-- operator exactly. Relations already accepted by the existing Core sort checker
-- are returned unchanged. Only a raw sort failure delegates to Core focusing, so
-- established UInt->Nat insertion can rescue admissible ordered UInt/Nat pairs
-- without normalizing or otherwise rewriting already-valid relations. Plain
-- relations need no claim environment, so the empty static context is exact here:
-- no claim identity, evidence, or authority can be introduced by this bridge.
-- Mixed-sort equality, projection, and unresolved names remain fail-closed.
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
      Left _ ->
        case canonicalizeProposition emptyStaticContext (stateCore state) proposition of
          Right (canonical, _) -> Just canonical
          Left _ -> Nothing
  _ -> Nothing
