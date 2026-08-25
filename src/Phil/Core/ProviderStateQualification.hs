{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderStateQualification
  ( ProviderStateRelationRevision (..)
  , ProviderAbstractStateKey (..)
  , ProviderImplementationStateKey (..)
  , ProviderStatePair (..)
  , ProviderImplementationStateTransition (..)
  , ProviderContractStateTransition (..)
  , ProviderStateRefinement (..)
  , CheckedProviderStateQualification (..)
  , ProviderStateQualificationError (..)
  , checkProviderStateSimulation
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualification
  ( CheckedProviderOperationQualification (..)
  , CheckedProviderSemanticQualification (..)
  , ProviderOperationKey
  , ProviderOutcomeKey
  )

-- | Stable identity of one abstract/concrete provider-state relation.  The
-- checker does not prescribe a theorem language for this relation; it checks
-- the exact finite relation facts supplied to the Phase 1 conformance layer.
newtype ProviderStateRelationRevision = ProviderStateRelationRevision
  { unProviderStateRelationRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderAbstractStateKey = ProviderAbstractStateKey
  { unProviderAbstractStateKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderImplementationStateKey = ProviderImplementationStateKey
  { unProviderImplementationStateKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | One exact pair admitted by the named provider-state relation α : J ~ A.
data ProviderStatePair = ProviderStatePair
  { providerStatePairImplementation :: ProviderImplementationStateKey
  , providerStatePairAbstract :: ProviderAbstractStateKey
  }
  deriving (Eq, Ord, Show)

-- | One reachable implementation transition for a qualified public provider
-- operation.  The implementation outcome key is interpreted through the exact
-- operation outcome correspondence already checked by PROV-001--005.
data ProviderImplementationStateTransition = ProviderImplementationStateTransition
  { providerImplementationStateTransitionOperation :: ProviderOperationKey
  , providerImplementationStateTransitionFrom :: ProviderImplementationStateKey
  , providerImplementationStateTransitionOutcome :: ProviderOutcomeKey
  , providerImplementationStateTransitionTo :: ProviderImplementationStateKey
  }
  deriving (Eq, Ord, Show)

-- | One public abstract transition allowed by the provider contract/state model.
data ProviderContractStateTransition = ProviderContractStateTransition
  { providerContractStateTransitionOperation :: ProviderOperationKey
  , providerContractStateTransitionFrom :: ProviderAbstractStateKey
  , providerContractStateTransitionOutcome :: ProviderOutcomeKey
  , providerContractStateTransitionTo :: ProviderAbstractStateKey
  }
  deriving (Eq, Ord, Show)

-- | Bounded Phase 1 state-refinement object.  Visible implementation initial
-- states must be mapped explicitly into admissible abstract initial states.  All
-- reachable implementation transitions must simulate allowed abstract
-- transitions while preserving the named relation.
data ProviderStateRefinement = ProviderStateRefinement
  { providerStateRelationRevision :: ProviderStateRelationRevision
  , providerStateRelatedPairs :: Set.Set ProviderStatePair
  , providerStateVisibleInitialImplementationStates
      :: Set.Set ProviderImplementationStateKey
  , providerStateAdmissibleInitialAbstractStates
      :: Set.Set ProviderAbstractStateKey
  , providerStateInitialCorrespondence
      :: Map.Map ProviderImplementationStateKey ProviderAbstractStateKey
  , providerStateImplementationTransitions
      :: Set.Set ProviderImplementationStateTransition
  , providerStateContractTransitions
      :: Set.Set ProviderContractStateTransition
  }
  deriving (Eq, Ord, Show)

data CheckedProviderStateQualification = CheckedProviderStateQualification
  { checkedProviderStateRelationRevision :: ProviderStateRelationRevision
  , checkedProviderStateContractRevisionMatches :: Bool
  , checkedProviderStateInitialization
      :: Map.Map ProviderImplementationStateKey ProviderAbstractStateKey
  , checkedProviderStateImplementationTransitions
      :: Set.Set ProviderImplementationStateTransition
  }
  deriving (Eq, Ord, Show)

data ProviderStateQualificationError
  = ProviderStateMissingInitialCorrespondence
      (Set.Set ProviderImplementationStateKey)
  | ProviderStateUnexpectedInitialCorrespondence
      (Set.Set ProviderImplementationStateKey)
  | ProviderStateInitialAbstractStateNotAdmissible
      ProviderImplementationStateKey ProviderAbstractStateKey
  | ProviderStateInitialPairOutsideRelation
      ProviderImplementationStateKey ProviderAbstractStateKey
  | ProviderStateTransitionUsesUnqualifiedOperation ProviderOperationKey
  | ProviderStateTransitionUsesUnmappedImplementationOutcome
      ProviderOperationKey ProviderOutcomeKey
  | ProviderStateTransitionStartsOutsideRelation
      ProviderImplementationStateTransition
  | ProviderStateTransitionNotSimulated
      ProviderImplementationStateTransition
      ProviderAbstractStateKey
      ProviderOutcomeKey
  deriving (Eq, Ord, Show)

-- | Check PROV-006 over an already accepted PROV-001--005 semantic provider
-- qualification.  The simulation is asymmetric: an implementation may realize
-- fewer abstract transitions, but every reachable implementation transition
-- from every related abstract pre-state must map to an allowed contract outcome
-- and end in a related abstract successor state.
checkProviderStateSimulation
  :: CheckedProviderSemanticQualification
  -> ProviderStateRefinement
  -> Either ProviderStateQualificationError CheckedProviderStateQualification
checkProviderStateSimulation qualified refinement = do
  checkInitialization
  mapM_ checkImplementationTransition
    (Set.toAscList (providerStateImplementationTransitions refinement))
  Right CheckedProviderStateQualification
    { checkedProviderStateRelationRevision = providerStateRelationRevision refinement
    , checkedProviderStateContractRevisionMatches = True
    , checkedProviderStateInitialization = providerStateInitialCorrespondence refinement
    , checkedProviderStateImplementationTransitions =
        providerStateImplementationTransitions refinement
    }
  where
    visibleInitial = providerStateVisibleInitialImplementationStates refinement
    initialCorrespondence = providerStateInitialCorrespondence refinement
    initialDomain = Map.keysSet initialCorrespondence
    missingInitial = Set.difference visibleInitial initialDomain
    unexpectedInitial = Set.difference initialDomain visibleInitial

    checkInitialization
      | not (Set.null missingInitial) =
          Left (ProviderStateMissingInitialCorrespondence missingInitial)
      | not (Set.null unexpectedInitial) =
          Left (ProviderStateUnexpectedInitialCorrespondence unexpectedInitial)
      | otherwise = mapM_ checkInitialPair (Map.toAscList initialCorrespondence)

    checkInitialPair (implementationState, abstractState)
      | not (Set.member abstractState
          (providerStateAdmissibleInitialAbstractStates refinement)) =
          Left (ProviderStateInitialAbstractStateNotAdmissible
            implementationState abstractState)
      | not (Set.member
          (ProviderStatePair implementationState abstractState)
          (providerStateRelatedPairs refinement)) =
          Left (ProviderStateInitialPairOutsideRelation
            implementationState abstractState)
      | otherwise = Right ()

    checkImplementationTransition transition = do
      operationQualification <- case Map.lookup
          (providerImplementationStateTransitionOperation transition)
          (checkedProviderOperations qualified) of
        Just value -> Right value
        Nothing -> Left (ProviderStateTransitionUsesUnqualifiedOperation
          (providerImplementationStateTransitionOperation transition))
      contractOutcome <- case Map.lookup
          (providerImplementationStateTransitionOutcome transition)
          (checkedProviderOutcomeCorrespondence operationQualification) of
        Just value -> Right value
        Nothing -> Left (ProviderStateTransitionUsesUnmappedImplementationOutcome
          (providerImplementationStateTransitionOperation transition)
          (providerImplementationStateTransitionOutcome transition))
      let relatedAbstractPreStates = Set.fromList
            [ providerStatePairAbstract pair
            | pair <- Set.toAscList (providerStateRelatedPairs refinement)
            , providerStatePairImplementation pair
                == providerImplementationStateTransitionFrom transition
            ]
      if Set.null relatedAbstractPreStates
        then Left (ProviderStateTransitionStartsOutsideRelation transition)
        else mapM_
          (checkAbstractSimulation transition contractOutcome)
          (Set.toAscList relatedAbstractPreStates)

    checkAbstractSimulation transition contractOutcome abstractPre =
      if any simulates (Set.toAscList (providerStateContractTransitions refinement))
        then Right ()
        else Left (ProviderStateTransitionNotSimulated
          transition abstractPre contractOutcome)
      where
        simulates contractTransition =
          providerContractStateTransitionOperation contractTransition
              == providerImplementationStateTransitionOperation transition
            && providerContractStateTransitionFrom contractTransition == abstractPre
            && providerContractStateTransitionOutcome contractTransition == contractOutcome
            && Set.member
              (ProviderStatePair
                (providerImplementationStateTransitionTo transition)
                (providerContractStateTransitionTo contractTransition))
              (providerStateRelatedPairs refinement)
