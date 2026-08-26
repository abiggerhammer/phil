{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.BoundaryCommitWitnesses
  ( uploadBoundaryCommitStageBundle
  , uploadBoundaryProtocolStageBundle
  , uploadReceiveTransfer
  , uploadSendTransfer
  , uploadClientSendTransition
  , uploadClientSendPredecessor
  , uploadClientSendSuccessor
  ) where

import qualified Data.Map.Strict as Map
import Phil.Examples.Phase1.ProtocolStateWitnesses
  ( receivePayloadTransition
  , uploadProtocolInstance
  , uploadProtocolStateStageBundle
  , uploadServerTransport
  )
import Phil.Examples.Phase1.SubjectWitnesses
  ( uploadClientPayloadSubject
  , uploadPayloadSubject
  )
import Phil.Systems.BoundaryCommitCorrespondence
import Phil.Systems.IR (BlockId (..), ValueId (..))
import Phil.Systems.ProtocolStateCorrespondence
import Phil.Systems.SubjectCorrespondence (SystemsValueRef (..))

uploadBoundaryCommitStageBundle :: Either String BoundaryCommitStageBundle
uploadBoundaryCommitStageBundle = do
  base <- uploadBoundaryProtocolStageBundle
  pure (makeBoundaryCommitStageBundle base (Map.fromList
    [ (boundaryTransferKey uploadReceiveTransfer, uploadReceiveTransfer)
    , (boundaryTransferKey uploadSendTransfer, uploadSendTransfer)
    ]))

uploadBoundaryProtocolStageBundle :: Either String ProtocolStateStageBundle
uploadBoundaryProtocolStageBundle = do
  base <- uploadProtocolStateStageBundle
  let endpoints = Map.insert uploadClientSendSuccessor clientSendSuccessorState
        (Map.insert uploadClientSendPredecessor clientSendPredecessorState
          (protocolStateStageEndpoints base))
      transitions = Map.insert
        (protocolTransitionKey uploadClientSendTransition)
        uploadClientSendTransition
        (protocolStateStageTransitions base)
      extended = makeProtocolStateStageBundle
        (protocolStateStageBase base) endpoints transitions
  case verifyProtocolStateStageBundle extended of
    Right () -> Right extended
    Left err -> Left ("extended upload protocol stage rejected: " <> show err)

uploadClientRole :: ProtocolRoleKey
uploadClientRole = ProtocolRoleKey "client"

uploadClientTransport, uploadClientPayload :: SystemsValueRef
uploadClientTransport = SystemsValueRef "UploadClient" (ValueId "client.transport")
uploadClientPayload = SystemsValueRef "UploadClient" (ValueId "client.payload")

uploadServerPayload, uploadServerLength :: SystemsValueRef
uploadServerPayload = SystemsValueRef "UploadServer" (ValueId "server.payload")
uploadServerLength = SystemsValueRef "UploadServer" (ValueId "server.begin_length")

uploadClientSendPredecessor, uploadClientSendSuccessor :: EndpointOccurrenceKey
uploadClientSendPredecessor = EndpointOccurrenceKey "upload.client.endpoint.before-payload-send"
uploadClientSendSuccessor = EndpointOccurrenceKey "upload.client.endpoint.after-payload-send"

clientSendPredecessorState, clientSendSuccessorState :: ProtocolEndpointState
clientSendPredecessorState = ProtocolEndpointState
  { protocolEndpointOccurrence = uploadClientSendPredecessor
  , protocolEndpointInstance = uploadProtocolInstance
  , protocolEndpointRole = uploadClientRole
  , protocolEndpointSession = LocalSessionRevision "upload.client.session.send-payload"
  }
clientSendSuccessorState = ProtocolEndpointState
  { protocolEndpointOccurrence = uploadClientSendSuccessor
  , protocolEndpointInstance = uploadProtocolInstance
  , protocolEndpointRole = uploadClientRole
  , protocolEndpointSession = LocalSessionRevision "upload.client.session.await-result"
  }

uploadClientSendTransition :: ProtocolTransitionBinding
uploadClientSendTransition = ProtocolTransitionBinding
  { protocolTransitionKey = ProtocolTransitionKey "upload.client.send-payload-exact"
  , protocolTransitionPredecessor = uploadClientSendPredecessor
  , protocolTransitionAction = ProtocolOpaqueAction "upload.client.send-payload-exact"
  , protocolTransitionTargetSite = ProtocolOperationSite
      "UploadClient" (BlockId "client.payload") 1
  , protocolTransitionTransport = uploadClientTransport
  , protocolTransitionOutcomes = Map.singleton
      "success" (ProtocolSuccessor uploadClientSendSuccessor)
  , protocolTransitionBasis = CheckedLegacyOpaqueProtocolBridge
      "phase0.endpoint.typestate.payload-exact-send.v1"
  }

uploadReceiveTransfer :: BoundaryTransferContract
uploadReceiveTransfer = BoundaryTransferContract
  { boundaryTransferKey = BoundaryTransferKey "upload.server.payload.receive-exact"
  , boundaryTransferDirection = BoundaryReceiveExact
  , boundaryTransferSourceFact = "payload.exact_receive"
  , boundaryTransferSubject = uploadPayloadSubject
  , boundaryTransferTargetSite = ProtocolTerminatorSite
      "UploadServer" (BlockId "server.payload")
  , boundaryTransferTransport = uploadServerTransport
  , boundaryTransferOwner = uploadServerPayload
  , boundaryTransferExpectedOwnerShape = "Bytes[begin.length]"
  , boundaryTransferLength = ExplicitBoundaryLength
      "begin.length" uploadServerLength
  , boundaryTransferProtocolTransition = protocolTransitionKey receivePayloadTransition
  , boundaryTransferCommitOutcome = "success"
  , boundaryTransferFailureOutcome = Just "failure"
  }

uploadSendTransfer :: BoundaryTransferContract
uploadSendTransfer = BoundaryTransferContract
  { boundaryTransferKey = BoundaryTransferKey "upload.client.payload.send-exact"
  , boundaryTransferDirection = BoundarySendExact
  , boundaryTransferSourceFact = "payload.exact_send"
  , boundaryTransferSubject = uploadClientPayloadSubject
  , boundaryTransferTargetSite = ProtocolOperationSite
      "UploadClient" (BlockId "client.payload") 1
  , boundaryTransferTransport = uploadClientTransport
  , boundaryTransferOwner = uploadClientPayload
  , boundaryTransferExpectedOwnerShape = "Bytes[payload.length]"
  , boundaryTransferLength = OwnerIndexedBoundaryLength
      "payload.length" "Bytes[payload.length]"
  , boundaryTransferProtocolTransition = protocolTransitionKey uploadClientSendTransition
  , boundaryTransferCommitOutcome = "success"
  , boundaryTransferFailureOutcome = Nothing
  }
