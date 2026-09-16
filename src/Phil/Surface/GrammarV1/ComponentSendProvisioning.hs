{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ComponentSendProvisioning
  ( GrammarV1ResolvedComponentSend (..)
  , GrammarV1ComponentSendProvisioningError (..)
  , grammarV1ResolveComponentSendProvisioning
  ) where

import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey
  )
import Phil.Core.ProcessRendezvous
  ( ProcessRendezvousSide (..)
  )
import Phil.Core.Protocol.Family
  ( ProtocolProjectionEvidence (..)
  )
import Phil.Core.Syntax
  ( Session (..)
  , Ty
  )
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
  ( GrammarV1ComponentProvisioningSource (..)
  , GrammarV1ProvisionedComponentParameter (..)
  , GrammarV1ResolvedComponentProvisioning (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.ComponentSendClose
  ( GrammarV1CheckedComponentSendClose (..)
  )

-- | Exact runtime-facing client send information derived by joining the checked
-- source body to the architecture provisioning carrier. The payload occurrence
-- remains explicit even when its mode is unrestricted, so later integration can
-- show which architecture entry supplied the sent value without pretending that
-- an affine/linear ownership transfer occurred.
data GrammarV1ResolvedComponentSend = GrammarV1ResolvedComponentSend
  { resolvedComponentSendPayloadParameter :: GrammarV1ProvisionedComponentParameter
  , resolvedComponentSendPayloadOccurrence :: ActivationOccurrenceKey
  , resolvedComponentSendEndpointParameter :: GrammarV1ProvisionedComponentParameter
  , resolvedComponentSendRendezvousSide :: ProcessRendezvousSide
  }
  deriving (Eq, Show)

data GrammarV1ComponentSendProvisioningError
  = GrammarV1ComponentSendParameterMissing GrammarV1BinderKey
  | GrammarV1ComponentSendParameterAmbiguous GrammarV1BinderKey
  | GrammarV1ComponentSendPayloadNotEntry GrammarV1ComponentProvisioningSource
  | GrammarV1ComponentSendEndpointNotProtocol GrammarV1ComponentProvisioningSource
  | GrammarV1ComponentSendEndpointSessionNotSend Session
  | GrammarV1ComponentSendPayloadTypeMismatch Ty Ty
  deriving (Eq, Show)

-- | Join the exact source-semantic `send payload on endpoint` plan to one already
-- resolved component occurrence. Binder keys are the join keys; display spelling
-- is never used to recover identity. The endpoint projection supplies exact
-- protocol instance/role/session identity and the source successor binder supplies
-- the runtime successor name.
grammarV1ResolveComponentSendProvisioning
  :: GrammarV1CheckedComponentSendClose
  -> GrammarV1ResolvedComponentProvisioning
  -> Either
      GrammarV1ComponentSendProvisioningError
      GrammarV1ResolvedComponentSend
grammarV1ResolveComponentSendProvisioning sourcePlan provisioning = do
  payloadParameter <- requireExactParameter
    (grammarV1ResolvedBinderKey (checkedComponentSendPayload sourcePlan))
  endpointParameter <- requireExactParameter
    (grammarV1ResolvedBinderKey (checkedComponentSendEndpoint sourcePlan))
  case provisionedComponentParameterSource payloadParameter of
    GrammarV1ComponentProvisioningEntry _ _ -> Right ()
    other -> Left (GrammarV1ComponentSendPayloadNotEntry other)
  projection <- case provisionedComponentParameterSource endpointParameter of
    GrammarV1ComponentProvisioningProtocolEndpoint _ value -> Right value
    other -> Left (GrammarV1ComponentSendEndpointNotProtocol other)
  let payloadType = checkedBindingType
        (provisionedComponentParameterCheckedMode payloadParameter)
      endpointSession = protocolProjectionSession projection
  messageType <- case endpointSession of
    Send _ ty _ -> Right ty
    other -> Left (GrammarV1ComponentSendEndpointSessionNotSend other)
  if payloadType == messageType
    then Right ()
    else Left (GrammarV1ComponentSendPayloadTypeMismatch messageType payloadType)
  let endpointBinder = provisionedComponentParameterBinder endpointParameter
      successorBinder = checkedComponentSendSuccessor sourcePlan
      side = ProcessRendezvousSide
        { rendezvousProcess = resolvedProvisioningProcessKey provisioning
        , rendezvousEndpoint = grammarV1ResolvedBinderCoreName endpointBinder
        , rendezvousSuccessor = grammarV1ResolvedBinderCoreName successorBinder
        , rendezvousInstance = protocolProjectionInstance projection
        , rendezvousRole = protocolProjectionRole projection
        }
  Right GrammarV1ResolvedComponentSend
    { resolvedComponentSendPayloadParameter = payloadParameter
    , resolvedComponentSendPayloadOccurrence =
        provisionedComponentParameterOccurrence payloadParameter
    , resolvedComponentSendEndpointParameter = endpointParameter
    , resolvedComponentSendRendezvousSide = side
    }
  where
    requireExactParameter key =
      case
        [ parameter
        | parameter <- resolvedProvisioningParameters provisioning
        , grammarV1ResolvedBinderKey
            (provisionedComponentParameterBinder parameter) == key
        ] of
        [] -> Left (GrammarV1ComponentSendParameterMissing key)
        [parameter] -> Right parameter
        _ -> Left (GrammarV1ComponentSendParameterAmbiguous key)
