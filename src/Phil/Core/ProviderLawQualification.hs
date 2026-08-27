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

import qualified ProviderLawQualificationKernel as Kernel
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
  | ProviderLawQualificationRepresentationMismatch Text
  deriving (Eq, Ord, Show)

-- | Check one implementation history against one provider-wide public law.
-- Every implementation event is first translated through the already-qualified
-- operation/outcome correspondence, then evaluated by the public law monitor.
-- The extracted kernel owns acceptance; the detailed traversal below is retained
-- only for result/error reconstruction and must agree with that decision.
checkProviderLawTrace
  :: CheckedProviderSemanticQualification
  -> ProviderLaw
  -> [ProviderImplementationEvent]
  -> Either ProviderLawQualificationError CheckedProviderLawTrace
checkProviderLawTrace qualified law implementationTrace
  | not (providerLawProjectionRoundTrips qualified law) =
      Left (ProviderLawQualificationRepresentationMismatch
        "provider law Map projection failed canonical round-trip")
  | providerLawKernelAccepts qualified law implementationTrace =
      case checkProviderLawTraceDetailed qualified law implementationTrace of
        Right checked -> Right checked
        Left _ -> Left (ProviderLawQualificationRepresentationMismatch
          "extracted provider law kernel accepted while diagnostic reconstruction rejected")
  | otherwise =
      case checkProviderLawTraceDetailed qualified law implementationTrace of
        Left err -> Left err
        Right _ -> Left (ProviderLawQualificationRepresentationMismatch
          "extracted provider law kernel rejected while diagnostic reconstruction accepted")

checkProviderLawTraceDetailed
  :: CheckedProviderSemanticQualification
  -> ProviderLaw
  -> [ProviderImplementationEvent]
  -> Either ProviderLawQualificationError CheckedProviderLawTrace
checkProviderLawTraceDetailed qualified law implementationTrace = do
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

providerLawKernelAccepts
  :: CheckedProviderSemanticQualification
  -> ProviderLaw
  -> [ProviderImplementationEvent]
  -> Bool
providerLawKernelAccepts qualified law implementationTrace =
  Kernel.decideProviderLawTrace
    (==)
    (==)
    (==)
    qualifiedOutcomes
    transitionProjection
    (providerLawInitialState law)
    traceProjection
  where
    qualifiedOutcomes =
      [ (operationKey,
          Map.toAscList
            (checkedProviderOutcomeCorrespondence operationQualification))
      | (operationKey, operationQualification) <-
          Map.toAscList (checkedProviderOperations qualified)
      ]
    transitionProjection =
      [ ( (state,
            ( providerPublicEventOperation event
            , providerPublicEventOutcome event
            ))
        , nextState
        )
      | ((state, event), nextState) <-
          Map.toAscList (providerLawTransitions law)
      ]
    traceProjection =
      [ ( providerImplementationEventOperation event
        , providerImplementationEventOutcome event
        )
      | event <- implementationTrace
      ]

providerLawProjectionRoundTrips
  :: CheckedProviderSemanticQualification
  -> ProviderLaw
  -> Bool
providerLawProjectionRoundTrips qualified law =
  and
    [ mapRoundTrips (checkedProviderOperations qualified)
    , all operationQualificationRoundTrips
        (Map.elems (checkedProviderOperations qualified))
    , mapRoundTrips (providerLawTransitions law)
    ]
  where
    operationQualificationRoundTrips operationQualification =
      mapRoundTrips (checkedProviderOutcomeCorrespondence operationQualification)

mapRoundTrips :: (Ord key, Eq value) => Map.Map key value -> Bool
mapRoundTrips values = Map.fromAscList (Map.toAscList values) == values

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