{-# LANGUAGE OverloadedStrings #-}

module Phil.IO.SignalCancellation
  ( HostSignalEvent (..)
  , SignalCancellationAdapterSpec (..)
  , CheckedSignalCancellation
  , checkedSignalCancellationEvent
  , checkedSignalCancellationProviderObservation
  , checkedSignalCancellationCapabilityObservation
  , checkedSignalCancellationBoundaryObservation
  , checkedSignalCancellationEntryObservation
  , SignalCancellationAdapterError (..)
  , checkSignalCancellationAdapter
  ) where

import Data.Text (Text)
import Phil.Core.Authority
  ( AuthorityCheckError
  , AuthorityExerciseSource
  , AuthorityRequirement
  , AuthorityState
  , CheckedAuthorityExercise
  , checkAuthorityExercise
  )
import Phil.Core.EnvironmentObservation
  ( CheckedEnvironmentObservation
  , EnvironmentObservationError
  , EnvironmentObservationKind (..)
  , EnvironmentObservationRelationKey
  , EnvironmentObservationSource (..)
  , checkEnvironmentObservation
  , emptyEnvironmentObservationContext
  , registerBoundaryEnvironmentObservation
  , registerCapabilityEnvironmentObservation
  , registerEntryEnvironmentObservation
  , registerProviderEnvironmentObservation
  )
import Phil.Core.ProviderQualification
  ( CheckedProviderSemanticQualification
  , ProviderOperationKey
  )

-- | Concrete host signal observed by the realization adapter.  This value is not
-- itself Phil semantic input: only 'checkSignalCancellationAdapter' may reify the
-- admitted SIGINT case through explicit semantic relations.
data HostSignalEvent
  = HostSignalSIGINT
  | HostSignalOther Text
  deriving (Eq, Ord, Show)

-- | Exact semantic route selected for the conventional SIGINT adapter.
--
-- All four identities are deliberately independent:
--
-- * provider relation: which qualified external operation observes the host event;
-- * capability relation: which possessed authority permits that observation;
-- * boundary relation: which source/architecture boundary admits the event;
-- * entry relation: which explicit architecture input receives the reified value.
data SignalCancellationAdapterSpec = SignalCancellationAdapterSpec
  { signalCancellationProviderRelation :: EnvironmentObservationRelationKey
  , signalCancellationCapabilityRelation :: EnvironmentObservationRelationKey
  , signalCancellationBoundaryRelation :: EnvironmentObservationRelationKey
  , signalCancellationEntryRelation :: EnvironmentObservationRelationKey
  , signalCancellationBoundaryIdentity :: Text
  , signalCancellationEntryIdentity :: Text
  }
  deriving (Eq, Ord, Show)

data CheckedSignalCancellation = CheckedSignalCancellation
  { checkedSignalCancellationEvent :: HostSignalEvent
  , checkedSignalCancellationProviderObservation :: CheckedEnvironmentObservation
  , checkedSignalCancellationCapabilityObservation :: CheckedEnvironmentObservation
  , checkedSignalCancellationBoundaryObservation :: CheckedEnvironmentObservation
  , checkedSignalCancellationEntryObservation :: CheckedEnvironmentObservation
  }
  deriving (Eq, Ord, Show)

data SignalCancellationAdapterError
  = SignalCancellationUnexpectedHostSignal HostSignalEvent
  | SignalCancellationAuthorityError AuthorityCheckError
  | SignalCancellationObservationError EnvironmentObservationError
  deriving (Eq, Show)

-- | Reify conventional host SIGINT into one checked Phil cancellation value.
--
-- The host event alone is intentionally insufficient.  Acceptance requires an
-- already qualified provider operation, an already possessed exact authority
-- relation, a named boundary relation, and a named entry relation.  The ordinary
-- EnvironmentObservation checker is exercised for every route; there is no
-- ambient signal fallback or backend-symbol name matching.
checkSignalCancellationAdapter
  :: SignalCancellationAdapterSpec
  -> CheckedProviderSemanticQualification
  -> ProviderOperationKey
  -> AuthorityRequirement
  -> AuthorityExerciseSource
  -> AuthorityState
  -> HostSignalEvent
  -> Either SignalCancellationAdapterError CheckedSignalCancellation
checkSignalCancellationAdapter
    spec checkedProvider providerOperation authorityRequirement authoritySource
    authorityState event = do
  case event of
    HostSignalSIGINT -> Right ()
    other -> Left (SignalCancellationUnexpectedHostSignal other)

  checkedExercise <- mapLeft SignalCancellationAuthorityError $
    checkAuthorityExercise authorityRequirement authoritySource authorityState

  context1 <- mapLeft SignalCancellationObservationError $
    registerProviderEnvironmentObservation
      (signalCancellationProviderRelation spec)
      sigintObservationKind
      checkedProvider
      providerOperation
      emptyEnvironmentObservationContext
  context2 <- mapLeft SignalCancellationObservationError $
    registerCapabilityEnvironmentObservation
      (signalCancellationCapabilityRelation spec)
      sigintObservationKind
      checkedExercise
      context1
  context3 <- mapLeft SignalCancellationObservationError $
    registerBoundaryEnvironmentObservation
      (signalCancellationBoundaryRelation spec)
      sigintObservationKind
      (signalCancellationBoundaryIdentity spec)
      context2
  context4 <- mapLeft SignalCancellationObservationError $
    registerEntryEnvironmentObservation
      (signalCancellationEntryRelation spec)
      sigintObservationKind
      (signalCancellationEntryIdentity spec)
      context3

  providerObservation <- checkedObservation
    (signalCancellationProviderRelation spec)
    context4
  capabilityObservation <- checkedObservation
    (signalCancellationCapabilityRelation spec)
    context4
  boundaryObservation <- checkedObservation
    (signalCancellationBoundaryRelation spec)
    context4
  entryObservation <- checkedObservation
    (signalCancellationEntryRelation spec)
    context4

  Right CheckedSignalCancellation
    { checkedSignalCancellationEvent = event
    , checkedSignalCancellationProviderObservation = providerObservation
    , checkedSignalCancellationCapabilityObservation = capabilityObservation
    , checkedSignalCancellationBoundaryObservation = boundaryObservation
    , checkedSignalCancellationEntryObservation = entryObservation
    }
  where
    checkedObservation key context =
      mapLeft SignalCancellationObservationError $
        checkEnvironmentObservation
          sigintObservationKind
          (ExplicitEnvironmentObservation key)
          context

sigintObservationKind :: EnvironmentObservationKind
sigintObservationKind = EnvironmentOtherObservation "signal.SIGINT"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
