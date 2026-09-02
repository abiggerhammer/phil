module Phil.Surface.GrammarV1.CallableOutcomePropositions
  ( grammarV1CallableOutcomeEnsures
  , grammarV1CallableOutcomeObligations
  ) where

import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.CallableOutcomeState
  ( grammarV1OutcomeResidueStateScopes
  )
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1CallableParameterScope
  )
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1OutcomeKind
  , GrammarV1OutcomeResidue (..)
  , GrammarV1OutcomeResidueClause (..)
  , GrammarV1Proposition
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve outcome-local postconditions as an ordered category per residue.
-- Every proposition is checked under the exact callable-parameter scope plus the
-- single explicit primitive branch-state telescope, when present. A residue with
-- no state clause uses parameter scope only. More than one state clause remains
-- non-competent here: #574 intentionally preserved repeated state clauses without
-- inventing a cardinality rule, so proposition checking may not arbitrarily pick
-- one of several candidate branch scopes.
grammarV1CallableOutcomeEnsures
  :: StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        FocusingError
        [(GrammarV1OutcomeKind, [(Proposition, [FocusStep])])])
grammarV1CallableOutcomeEnsures =
  grammarV1CallableOutcomePropositionCategory select
  where
    select clause = case clause of
      GrammarV1OutcomeEnsures proposition -> Just proposition
      _ -> Nothing

-- | Preserve outcome-local residual obligations separately from postconditions.
-- The same exact branch scope and Core focusing seam are reused; no obligation is
-- reclassified as an ensured/discharged fact by this bridge.
grammarV1CallableOutcomeObligations
  :: StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        FocusingError
        [(GrammarV1OutcomeKind, [(Proposition, [FocusStep])])])
grammarV1CallableOutcomeObligations =
  grammarV1CallableOutcomePropositionCategory select
  where
    select clause = case clause of
      GrammarV1OutcomeObligation proposition -> Just proposition
      _ -> Nothing

grammarV1CallableOutcomePropositionCategory
  :: (GrammarV1OutcomeResidueClause -> Maybe (Located GrammarV1Proposition))
  -> StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        FocusingError
        [(GrammarV1OutcomeKind, [(Proposition, [FocusStep])])])
grammarV1CallableOutcomePropositionCategory select staticContext state source = do
  (_, parameterState) <- grammarV1CallableParameterScope state source
  checkedResidues <- mapM (checkResidue parameterState) residues
  pure (sequence checkedResidues)
  where
    residues =
      [ residue
      | Located _ (GrammarV1CallableOutcomeResidue residue) <- grammarV1CallableClauses source
      ]

    checkResidue parameterState (Located _ residue) = do
      stateScopes <- grammarV1OutcomeResidueStateScopes parameterState residue
      branchState <- case stateScopes of
        [] -> Just parameterState
        [(_, scopedState)] -> Just scopedState
        _ -> Nothing
      checked <- mapM
        (\proposition ->
          grammarV1CheckedProposition
            staticContext
            branchState
            (locatedValue proposition))
        [ proposition
        | Located _ clause <- grammarV1OutcomeResidueClauses residue
        , Just proposition <- [select clause]
        ]
      pure $ fmap
        (\propositions ->
          ( locatedValue (grammarV1OutcomeResidueKind residue)
          , propositions
          ))
        (sequence checked)
