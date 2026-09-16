{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessEndpointClosure
  ( ProcessEndpointClosureError (..)
  , closeProcessEndpointState
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.Process
  ( ActivationStatus (..)
  , ProcessKey
  , ProcessNetwork (..)
  , ProcessOccurrence (..)
  )
import Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey
  )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  )
import Phil.Core.Protocol
  ( ProtocolActionRequest (..)
  , ProtocolCheckError
  , ProtocolContext
  , ProtocolInstanceRevision
  , ProtocolRoleKey
  , checkedProtocolContext
  , checkProtocolAction
  )
import Phil.Core.Syntax
  ( Name
  , Outcome
  )

data ProcessEndpointClosureError
  = EndpointClosureUnknownProcess ProcessKey
  | EndpointClosureProcessNotActive ProcessKey ActivationStatus
  | EndpointClosureMissingProtocolContext ProcessKey
  | EndpointClosureOccurrenceUnknown ProcessKey Name
  | EndpointClosureOccurrenceAmbiguous ProcessKey Name [ActivationOccurrenceKey]
  | EndpointClosureProtocolError ProcessKey ProtocolCheckError
  deriving (Eq, Show)

-- | Close one live protocol endpoint and retire the exact restricted-owner
-- occurrence that named it. The protocol/resource transition and owner-ledger
-- retirement succeed together or no successor state is returned.
closeProcessEndpointState
  :: ProcessNetwork
  -> ProcessCommunicationState
  -> ProcessKey
  -> Name
  -> ProtocolInstanceRevision
  -> ProtocolRoleKey
  -> Outcome
  -> Either ProcessEndpointClosureError ProcessCommunicationState
closeProcessEndpointState network state processKey endpoint instanceRevision role outcome = do
  requireActive network processKey
  context <- maybe
    (Left (EndpointClosureMissingProtocolContext processKey))
    Right
    (Map.lookup processKey (communicationProtocolContexts state))
  occurrence <- uniqueEndpointOccurrence
    (communicationRestrictedOwners state)
    processKey
    endpoint
  step <- mapLeft (EndpointClosureProtocolError processKey) $
    checkProtocolAction
      (ProtocolCloseRequest endpoint instanceRevision role outcome)
      context
  let contexts = Map.insert processKey
        (checkedProtocolContext step)
        (communicationProtocolContexts state)
      owners = Map.delete occurrence (communicationRestrictedOwners state)
  pure state
    { communicationProtocolContexts = contexts
    , communicationRestrictedOwners = owners
    }

requireActive
  :: ProcessNetwork
  -> ProcessKey
  -> Either ProcessEndpointClosureError ()
requireActive network processKey =
  case Map.lookup processKey (processNetworkPopulation network) of
    Nothing -> Left (EndpointClosureUnknownProcess processKey)
    Just occurrence ->
      case processOccurrenceActivation occurrence of
        Active -> Right ()
        status -> Left (EndpointClosureProcessNotActive processKey status)

uniqueEndpointOccurrence
  :: Map.Map ActivationOccurrenceKey (ProcessKey, Name)
  -> ProcessKey
  -> Name
  -> Either ProcessEndpointClosureError ActivationOccurrenceKey
uniqueEndpointOccurrence owners processKey endpoint =
  case matching of
    [] -> Left (EndpointClosureOccurrenceUnknown processKey endpoint)
    [occurrence] -> Right occurrence
    occurrences -> Left
      (EndpointClosureOccurrenceAmbiguous processKey endpoint occurrences)
  where
    matching =
      [ occurrence
      | (occurrence, (ownerProcess, ownerName)) <- Map.toList owners
      , ownerProcess == processKey
      , ownerName == endpoint
      ]

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
