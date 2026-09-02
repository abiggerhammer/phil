module Phil.Surface.GrammarV1.CallableCalleeTransition
  ( grammarV1CalleeTransition
  , grammarV1CallableCalleeTransitions
  , grammarV1OutcomeCalleeTransitions
  ) where

import Phil.Core.Callable
  ( CalleeTransition (..)
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1CalleeTransition (..)
  , GrammarV1OutcomeResidue (..)
  , GrammarV1OutcomeResidueClause (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve the exact callable lifecycle choices that already have a direct
-- Core carrier. Preserve/consume map one-for-one to Core. Replace remains
-- outside this bridge because Core requires an exact InterfaceRevision and an
-- optional semantic CallableStateKey, neither of which may be invented from a
-- source replacement spelling or term expression.
grammarV1CalleeTransition
  :: GrammarV1CalleeTransition
  -> Maybe CalleeTransition
grammarV1CalleeTransition source = case source of
  GrammarV1CalleePreserve -> Just PreserveCallee
  GrammarV1CalleeConsume -> Just ConsumeCallee
  GrammarV1CalleeReplace _ _ -> Nothing

-- | Preserve all top-level callable callee clauses in source order without
-- deciding declaration-level cardinality. Exact absence is Just []; if any
-- transition is outside the current competence boundary, the projection fails
-- closed rather than dropping or reinterpreting that clause.
grammarV1CallableCalleeTransitions
  :: GrammarV1CallableContractDecl
  -> Maybe [CalleeTransition]
grammarV1CallableCalleeTransitions source =
  mapM
    (grammarV1CalleeTransition . locatedValue)
    [ transition
    | Located _ (GrammarV1CallableCallee transition) <-
        grammarV1CallableClauses source
    ]

-- | Apply the same exact transition bridge to one outcome-residue clause list.
-- Branch-sensitive cardinality/state consistency remains the competent callable
-- outcome checker's responsibility; this projection only preserves the ordered
-- transition category already present in the source.
grammarV1OutcomeCalleeTransitions
  :: GrammarV1OutcomeResidue
  -> Maybe [CalleeTransition]
grammarV1OutcomeCalleeTransitions source =
  mapM
    (grammarV1CalleeTransition . locatedValue)
    [ transition
    | Located _ (GrammarV1OutcomeCallee transition) <-
        grammarV1OutcomeResidueClauses source
    ]
