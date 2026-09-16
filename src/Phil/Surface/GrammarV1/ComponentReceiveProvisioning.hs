module Phil.Surface.GrammarV1.ComponentReceiveProvisioning
  ( GrammarV1ResolvedComponentReceive (..)
  , GrammarV1ComponentReceiveProvisioningError (..)
  , grammarV1ResolveComponentReceiveProvisioning
  ) where

import Phil.Core.Focusing (FocusingError)
import Phil.Core.ProcessRendezvous
  ( ProcessRendezvousSide (..)
  )
import Phil.Core.Protocol.Family
  ( ProtocolProjectionEvidence (..)
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Session (..)
  , Ty
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
  ( GrammarV1ComponentProvisioningSource (..)
  , GrammarV1ProvisionedComponentParameter (..)
  , GrammarV1ResolvedComponentProvisioning (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.ComponentReceiveClose
  ( GrammarV1CheckedComponentReceiveClose (..)
  )

-- | Runtime-facing server receive information derived from the exact source
-- receive/close plan plus architecture provisioning. The received value remains a
-- source binder rather than being invented by the runtime bridge.
data GrammarV1ResolvedComponentReceive = GrammarV1ResolvedComponentReceive
  { resolvedComponentReceiveEndpointParameter :: GrammarV1ProvisionedComponentParameter
  , resolvedComponentReceivePayloadBinder :: GrammarV1ResolvedBinder
  , resolvedComponentReceiveRendezvousSide :: ProcessRendezvousSide
  }
  deriving (Eq, Show)

data GrammarV1ComponentReceiveProvisioningError
  = GrammarV1ComponentReceiveParameterMissing GrammarV1BinderKey
  | GrammarV1ComponentReceiveParameterAmbiguous GrammarV1BinderKey
  | GrammarV1ComponentReceiveEndpointNotProtocol GrammarV1ComponentProvisioningSource
  | GrammarV1ComponentReceiveEndpointSessionNotReceive Session
  | GrammarV1ComponentReceiveWrittenTypeNonCompetent
  | GrammarV1ComponentReceiveWrittenTypeFocusingError FocusingError
  | GrammarV1ComponentReceiveMessageTypeMismatch Ty Ty
  deriving (Eq, Show)

-- | Join the exact source-semantic `receive T on endpoint` plan to one resolved
-- component occurrence. The source-written message type is checked through the
-- ordinary Grammar-v1 type authority and must equal the projected Receive message
-- type before a rendezvous side can be produced.
grammarV1ResolveComponentReceiveProvisioning
  :: StaticContext
  -> GrammarV1CheckedComponentReceiveClose
  -> GrammarV1ResolvedComponentProvisioning
  -> Either
      GrammarV1ComponentReceiveProvisioningError
      GrammarV1ResolvedComponentReceive
grammarV1ResolveComponentReceiveProvisioning staticContext sourcePlan provisioning = do
  endpointParameter <- requireExactParameter
    (grammarV1ResolvedBinderKey (checkedComponentReceiveEndpoint sourcePlan))
  projection <- case provisionedComponentParameterSource endpointParameter of
    GrammarV1ComponentProvisioningProtocolEndpoint _ value -> Right value
    other -> Left (GrammarV1ComponentReceiveEndpointNotProtocol other)
  let endpointSession = protocolProjectionSession projection
  expectedMessageType <- case endpointSession of
    Receive _ ty _ -> Right ty
    other -> Left (GrammarV1ComponentReceiveEndpointSessionNotReceive other)
  writtenType <- case grammarV1CheckedType
      staticContext
      emptySurfaceState
      (checkedComponentReceiveWrittenType sourcePlan) of
    Nothing -> Left GrammarV1ComponentReceiveWrittenTypeNonCompetent
    Just (Left err) -> Left (GrammarV1ComponentReceiveWrittenTypeFocusingError err)
    Just (Right (ty, _)) -> Right ty
  if writtenType == expectedMessageType
    then Right ()
    else Left
      (GrammarV1ComponentReceiveMessageTypeMismatch expectedMessageType writtenType)
  let endpointBinder = provisionedComponentParameterBinder endpointParameter
      successorBinder = checkedComponentReceiveSuccessor sourcePlan
      side = ProcessRendezvousSide
        { rendezvousProcess = resolvedProvisioningProcessKey provisioning
        , rendezvousEndpoint = grammarV1ResolvedBinderCoreName endpointBinder
        , rendezvousSuccessor = grammarV1ResolvedBinderCoreName successorBinder
        , rendezvousInstance = protocolProjectionInstance projection
        , rendezvousRole = protocolProjectionRole projection
        }
  Right GrammarV1ResolvedComponentReceive
    { resolvedComponentReceiveEndpointParameter = endpointParameter
    , resolvedComponentReceivePayloadBinder = checkedComponentReceivePayload sourcePlan
    , resolvedComponentReceiveRendezvousSide = side
    }
  where
    requireExactParameter key =
      case
        [ parameter
        | parameter <- resolvedProvisioningParameters provisioning
        , grammarV1ResolvedBinderKey
            (provisionedComponentParameterBinder parameter) == key
        ] of
        [] -> Left (GrammarV1ComponentReceiveParameterMissing key)
        [parameter] -> Right parameter
        _ -> Left (GrammarV1ComponentReceiveParameterAmbiguous key)
