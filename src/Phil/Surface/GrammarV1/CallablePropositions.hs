module Phil.Surface.GrammarV1.CallablePropositions
  ( grammarV1CallableRequires
  , grammarV1CallableEnsures
  , grammarV1CallableObligations
  , grammarV1CallableAssumptions
  ) where

import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1CallableParameterScope
  )
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1Proposition
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve callable preconditions as their own ordered semantic category.
-- Parameter scope is shared exactly with checked signature elaboration. Every
-- complete structural proposition delegates once to Core focusing; one source
-- non-competent proposition rejects the whole projection as Nothing, while a
-- Core semantic rejection remains a distinct Left.
grammarV1CallableRequires
  :: StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe (Either FocusingError [(Proposition, [FocusStep])])
grammarV1CallableRequires =
  grammarV1CallablePropositionCategory select
  where
    select clause = case clause of
      GrammarV1CallableRequires proposition -> Just proposition
      _ -> Nothing

-- | Preserve callable postconditions separately from every other proposition
-- category; source order and exact Core focusing traces are retained.
grammarV1CallableEnsures
  :: StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe (Either FocusingError [(Proposition, [FocusStep])])
grammarV1CallableEnsures =
  grammarV1CallablePropositionCategory select
  where
    select clause = case clause of
      GrammarV1CallableEnsures proposition -> Just proposition
      _ -> Nothing

-- | Preserve callable residual obligations as a distinct ordered category.
-- Nothing in this bridge can reclassify an obligation as a postcondition,
-- assumption, effect, or discharged fact.
grammarV1CallableObligations
  :: StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe (Either FocusingError [(Proposition, [FocusStep])])
grammarV1CallableObligations =
  grammarV1CallablePropositionCategory select
  where
    select clause = case clause of
      GrammarV1CallableObligation proposition -> Just proposition
      _ -> Nothing

-- | Preserve callable assumptions separately and check their propositions under
-- the exact same lexical parameter environment used by the callable signature.
grammarV1CallableAssumptions
  :: StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe (Either FocusingError [(Proposition, [FocusStep])])
grammarV1CallableAssumptions =
  grammarV1CallablePropositionCategory select
  where
    select clause = case clause of
      GrammarV1CallableAssumes proposition -> Just proposition
      _ -> Nothing

grammarV1CallablePropositionCategory
  :: (GrammarV1CallableClause -> Maybe (Located GrammarV1Proposition))
  -> StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe (Either FocusingError [(Proposition, [FocusStep])])
grammarV1CallablePropositionCategory select staticContext state source = do
  (_, scopedState) <- grammarV1CallableParameterScope state source
  checked <- mapM elaborate selected
  pure (sequence checked)
  where
    selected =
      [ proposition
      | Located _ clause <- grammarV1CallableClauses source
      , Just proposition <- [select clause]
      ]
    elaborate proposition =
      grammarV1CheckedProposition
        staticContext
        scopedState
        (locatedValue proposition)
