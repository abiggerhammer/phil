module Phil.Surface.GrammarV1.CallableOutcomeState
  ( grammarV1OutcomeResidueStateScopes
  , grammarV1OutcomeResidueStateTelescopes
  , grammarV1CallableOutcomeStateTelescopes
  ) where

import Phil.Core.Syntax
  ( Name
  , Ty
  )
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1CallableParameterScope
  , grammarV1InsertPrimitiveBinding
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1OutcomeKind
  , GrammarV1OutcomeResidue (..)
  , GrammarV1OutcomeResidueClause (..)
  , GrammarV1StateSlot (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Elaborate each explicit outcome-state telescope independently under the same
-- callable parameter scope and retain the resulting temporary lexical state.
-- Repeated state clauses remain repeated semantic projections in source order:
-- this bridge neither merges them nor invents a cardinality rule. Within one
-- telescope, primitive state slots are inserted in source order through the
-- ordinary binding authority, so duplicate names fail closed. The temporary
-- states are exposed only so sibling outcome semantics can reuse the exact same
-- branch scope rather than reconstructing it differently.
grammarV1OutcomeResidueStateScopes
  :: SurfaceState
  -> GrammarV1OutcomeResidue
  -> Maybe [([(Name, Ty)], SurfaceState)]
grammarV1OutcomeResidueStateScopes parameterState source =
  mapM (elaborateSlots parameterState)
    [ slots
    | Located _ (GrammarV1OutcomeState slots) <- grammarV1OutcomeResidueClauses source
    ]

-- | Preserve only the explicit state telescopes for callers that do not need the
-- temporary lexical environment. This is a projection of
-- grammarV1OutcomeResidueStateScopes and therefore shares exactly the same
-- primitive competence and duplicate-binding behavior.
grammarV1OutcomeResidueStateTelescopes
  :: SurfaceState
  -> GrammarV1OutcomeResidue
  -> Maybe [[(Name, Ty)]]
grammarV1OutcomeResidueStateTelescopes parameterState source =
  map fst <$> grammarV1OutcomeResidueStateScopes parameterState source

-- | Preserve the source order and outcome kind of every branch-sensitive residue
-- while projecting only its explicit primitive state telescopes. Exact absence of
-- outcome residues is Just []. A residue with no state clause contributes an
-- empty telescope list. Generic/requirement-bearing callables and any state slot
-- outside the current primitive-mode competence fail closed via the shared
-- callable scope authority.
grammarV1CallableOutcomeStateTelescopes
  :: SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe [(GrammarV1OutcomeKind, [[(Name, Ty)]])]
grammarV1CallableOutcomeStateTelescopes state source = do
  (_, parameterState) <- grammarV1CallableParameterScope state source
  mapM (elaborateResidue parameterState)
    [ residue
    | Located _ (GrammarV1CallableOutcomeResidue residue) <- grammarV1CallableClauses source
    ]
  where
    elaborateResidue parameterState (Located _ residue) = do
      telescopes <- grammarV1OutcomeResidueStateTelescopes parameterState residue
      pure
        ( locatedValue (grammarV1OutcomeResidueKind residue)
        , telescopes
        )

elaborateSlots
  :: SurfaceState
  -> [Located GrammarV1StateSlot]
  -> Maybe ([(Name, Ty)], SurfaceState)
elaborateSlots = go []
  where
    go reversed state [] = Just (reverse reversed, state)
    go reversed state (Located _ slot : rest) = do
      ((slotName, ty), next) <- grammarV1InsertPrimitiveBinding
        (grammarV1StateSlotName slot)
        (grammarV1StateSlotType slot)
        state
      go ((slotName, ty) : reversed) next rest
