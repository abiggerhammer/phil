{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderLawQualification
  ( ProviderLawRevision (..)
  , ProviderLawStateKey (..)
  , ProviderImplementationTraceKey (..)
  , ProviderImplementationEvent (..)
  , ProviderPublicEvent (..)
  , ProviderLaw (..)
  , CheckedProviderLawTrace (..)
  , CheckedProviderLawCorpus (..)
  , ProviderLawQualificationError (..)
  , checkProviderLawTrace
  , checkProviderLawCorpus
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.ProviderQualification
  ( CheckedProviderOperationQualification (..)
  , CheckedProviderSemanticQualification (..)
  , ProviderOperationKey
  , ProviderOutcomeKey
  )

newtype ProviderLawRevision = ProviderLawRevision
  { unProviderLawRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderLawStateKey = ProviderLawStateKey
  { unProviderLawStateKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProviderImplementationTraceKey = ProviderImplementationTraceKey
  { unProviderImplementationTraceKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | One implementation-level provider event. Outcome identity is interpreted
-- only through the exact operation correspondence already accepted by the
-- semantic provider qualification.
data ProviderImplementationEvent = ProviderImplementationEvent
  { providerImplementationEventOperation :: ProviderOperationKey
  , providerImplementationEventOutcome :: ProviderOutcomeKey
  }
  deriving (Eq, Ord, Show)

-- | Public semantic event seen by a provider-wide law after exact outcome
-- translation. Implementation symbols, helper callables, and concrete state are
-- intentionally absent.
data ProviderPublicEvent = ProviderPublicEvent
  { providerPublicEventOperation :: ProviderOperationKey
  , providerPublicEventOutcome :: ProviderOutcomeKey
  }
  deriving (Eq, Ord, Show)

-- | Deterministic public-history monitor for one provider-wide law. Missing
-- transitions are illegal histories. The monitor state is law-specific logical
-- history state, not provider implementation state from PROV-006.
data ProviderLaw = ProviderLaw
  { providerLawRevision :: ProviderLawRevision
  , providerLawInitialState :: ProviderLawStateKey
  , providerLawTransitions
      :: Map.Map (ProviderLawStateKey, ProviderPublicEvent) ProviderLawStateKey
  }
  deriving (Eq, Ord, Show)

data CheckedProviderLawTrace = CheckedProviderLawTrace
  { checkedProviderLawRevision :: ProviderLawRevision
  , checkedProviderLawPublicTrace :: [ProviderPublicEvent]
  , checkedProviderLawFinalState :: ProviderLawStateKey
  }
  deriving (Eq, Ord, Show)

data CheckedProviderLawCorpus = CheckedProviderLawCorpus
  { checkedProviderLawCorpusRevision :: ProviderLawRevision
  , checkedProviderLawTraces
      :: Map.Map ProviderImplementationTraceKey CheckedProviderLawTrace
  }
  deriving (Eq, Ord, Show)

data ProviderLawQualificationError
  = ProviderLawTraceUsesUnqualifiedOperation ProviderOperationKey
  | ProviderLawTraceUsesUnmappedImplementationOutcome
      ProviderOperationKey ProviderOutcomeKey
  | ProviderLawViolation
      ProviderLawRevision
      Int
      ProviderLawStateKey
      ProviderPublicEvent
  deriving (Eq, Ord, Show)

-- | Check one implementation history against one provider-wide public law.
-- Every implementation event is first translated through the already-qualified
-- operation/outcome correspondence, then evaluated by the public law monitor.
-- This is precisely the layer that can reject a sequence even when every event
-- is independently valid under per-operation callable refinement.
checkProviderLawTrace
  :: CheckedProviderSemanticQualification
  -> ProviderLaw
  -> [ProviderImplementationEvent]
  -> Either ProviderLawQualificationError CheckedProviderLawTrace
checkProviderLawTrace qualified law implementationTrace = do
  publicTrace <- mapM translateEvent implementationTrace
  finalState <- runLaw 0 (providerLawInitialState law) publicTrace
  Right CheckedProviderLawTrace
    { checkedProviderLawRevision = providerLawRevision law
    , checkedProviderLawPublicTrace = publicTrace
    , checkedProviderLawFinalState = finalState
    }
  where
    translateEvent event = do
      operationQualification <- case Map.lookup
          (providerImplementationEventOperation event)
          (checkedProviderOperations qualified) of
        Just value -> Right value
        Nothing -> Left (ProviderLawTraceUsesUnqualifiedOperation
          (providerImplementationEventOperation event))
      publicOutcome <- case Map.lookup
          (providerImplementationEventOutcome event)
          (checkedProviderOutcomeCorrespondence operationQualification) of
        Just value -> Right value
        Nothing -> Left (ProviderLawTraceUsesUnmappedImplementationOutcome
          (providerImplementationEventOperation event)
          (providerImplementationEventOutcome event))
      Right ProviderPublicEvent
        { providerPublicEventOperation = providerImplementationEventOperation event
        , providerPublicEventOutcome = publicOutcome
        }

    runLaw _ state [] = Right state
    runLaw index state (event : rest) =
      case Map.lookup (state, event) (providerLawTransitions law) of
        Just nextState -> runLaw (index + 1) nextState rest
        Nothing -> Left (ProviderLawViolation
          (providerLawRevision law)
          index
          state
          event)

-- | Check a canonically keyed law-evidence corpus. Completeness of the corpus or
-- a proof/model-checking argument that it covers all reachable histories is a
-- separate qualification-evidence obligation; this function gives that evidence
-- layer one exact semantic law evaluator to target.
checkProviderLawCorpus
  :: CheckedProviderSemanticQualification
  -> ProviderLaw
  -> Map.Map ProviderImplementationTraceKey [ProviderImplementationEvent]
  -> Either ProviderLawQualificationError CheckedProviderLawCorpus
checkProviderLawCorpus qualified law traces = do
  checked <- Map.traverseWithKey
    (\_ trace -> checkProviderLawTrace qualified law trace)
    traces
  Right CheckedProviderLawCorpus
    { checkedProviderLawCorpusRevision = providerLawRevision law
    , checkedProviderLawTraces = checked
    }
