{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.ProtocolStateWitnesses
  ( uploadProtocolStateStageBundle
  , uploadProtocolInstance
  , uploadServerRole
  , uploadServerTransport
  , serverEp0
  , serverEp1
  , serverEp2
  , serverEp3
  , serverEp4
  , serverEp5
  , serverEp6
  , receiveHelloTransition
  , selectVersionTransition
  , receiveBeginTransition
  , selectProceedTransition
  , receivePayloadChoiceTransition
  , receivePayloadTransition
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Examples.Phase1.BranchResourceWitnesses
  ( uploadBranchResourceStageBundle
  )
import Phil.Systems.ControlStateProjection
  ( makeControlStateStageBundle
  )
import Phil.Systems.IR (BlockId (..), ValueId (..))
import Phil.Systems.ProtocolStateCorrespondence
import Phil.Systems.SubjectCorrespondence (SystemsValueRef (..))

uploadProtocolStateStageBundle :: Either String ProtocolStateStageBundle
uploadProtocolStateStageBundle = do
  branchBase <- uploadBranchResourceStageBundle
  let controlBase = makeControlStateStageBundle branchBase Map.empty Map.empty Map.empty
  pure (makeProtocolStateStageBundle controlBase endpointRegistry transitionRegistry)

uploadProtocolInstance :: ProtocolInstanceRevision
uploadProtocolInstance = ProtocolInstanceRevision "protocol.upload.phase0.instance.v1"

uploadServerRole :: ProtocolRoleKey
uploadServerRole = ProtocolRoleKey "server"

uploadServerTransport :: SystemsValueRef
uploadServerTransport = SystemsValueRef "UploadServer" (ValueId "server.transport")

serverEp0, serverEp1, serverEp2, serverEp3 :: EndpointOccurrenceKey
serverEp4, serverEp5, serverEp6 :: EndpointOccurrenceKey
serverEp0 = EndpointOccurrenceKey "upload.server.endpoint.0"
serverEp1 = EndpointOccurrenceKey "upload.server.endpoint.1"
serverEp2 = EndpointOccurrenceKey "upload.server.endpoint.2"
serverEp3 = EndpointOccurrenceKey "upload.server.endpoint.3"
serverEp4 = EndpointOccurrenceKey "upload.server.endpoint.4"
serverEp5 = EndpointOccurrenceKey "upload.server.endpoint.5"
serverEp6 = EndpointOccurrenceKey "upload.server.endpoint.6"

endpointRegistry :: Map.Map EndpointOccurrenceKey ProtocolEndpointState
endpointRegistry = Map.fromList
  [ endpoint serverEp0 "upload.server.session.await-hello"
  , endpoint serverEp1 "upload.server.session.choose-version"
  , endpoint serverEp2 "upload.server.session.await-begin"
  , endpoint serverEp3 "upload.server.session.begin-policy-choice"
  , endpoint serverEp4 "upload.server.session.await-payload-choice"
  , endpoint serverEp5 "upload.server.session.await-payload-bytes"
  , endpoint serverEp6 "upload.server.session.await-final-result"
  ]

endpoint :: EndpointOccurrenceKey -> Text -> (EndpointOccurrenceKey, ProtocolEndpointState)
endpoint occurrence session =
  ( occurrence
  , ProtocolEndpointState
      { protocolEndpointOccurrence = occurrence
      , protocolEndpointInstance = uploadProtocolInstance
      , protocolEndpointRole = uploadServerRole
      , protocolEndpointSession = LocalSessionRevision session
      }
  )

transitionRegistry :: Map.Map ProtocolTransitionKey ProtocolTransitionBinding
transitionRegistry = Map.fromList
  [ pair receiveHelloTransition
  , pair selectVersionTransition
  , pair receiveBeginTransition
  , pair selectProceedTransition
  , pair receivePayloadChoiceTransition
  , pair receivePayloadTransition
  ]
  where
    pair transition = (protocolTransitionKey transition, transition)

receiveHelloTransition :: ProtocolTransitionBinding
receiveHelloTransition = ProtocolTransitionBinding
  { protocolTransitionKey = ProtocolTransitionKey "upload.server.receive-hello"
  , protocolTransitionPredecessor = serverEp0
  , protocolTransitionAction = ProtocolReceiveCommit "Hello"
  , protocolTransitionTargetSite = ProtocolOperationSite
      "UploadServer" (BlockId "server.hello.commit") 0
  , protocolTransitionTransport = uploadServerTransport
  , protocolTransitionOutcomes = Map.singleton "success" (ProtocolSuccessor serverEp1)
  , protocolTransitionBasis = CheckedProtocolCorrespondence
      "phase0.endpoint.typestate.hello-commit.v1"
  }

selectVersionTransition :: ProtocolTransitionBinding
selectVersionTransition = opaqueTransition
  "upload.server.select-version"
  serverEp1
  (ProtocolOperationSite "UploadServer" (BlockId "server.version") 0)
  (Map.singleton "success" (ProtocolSuccessor serverEp2))
  "phase0.endpoint.typestate.version-select.v1"

receiveBeginTransition :: ProtocolTransitionBinding
receiveBeginTransition = ProtocolTransitionBinding
  { protocolTransitionKey = ProtocolTransitionKey "upload.server.receive-begin"
  , protocolTransitionPredecessor = serverEp2
  , protocolTransitionAction = ProtocolReceiveCommit "Begin"
  , protocolTransitionTargetSite = ProtocolOperationSite
      "UploadServer" (BlockId "server.begin.commit") 0
  , protocolTransitionTransport = uploadServerTransport
  , protocolTransitionOutcomes = Map.singleton "success" (ProtocolSuccessor serverEp3)
  , protocolTransitionBasis = CheckedProtocolCorrespondence
      "phase0.endpoint.typestate.begin-commit.v1"
  }

selectProceedTransition :: ProtocolTransitionBinding
selectProceedTransition = opaqueTransition
  "upload.server.select-proceed"
  serverEp3
  (ProtocolOperationSite "UploadServer" (BlockId "server.proceed") 0)
  (Map.singleton "success" (ProtocolSuccessor serverEp4))
  "phase0.endpoint.typestate.proceed-select.v1"

receivePayloadChoiceTransition :: ProtocolTransitionBinding
receivePayloadChoiceTransition = opaqueTransition
  "upload.server.receive-payload-choice"
  serverEp4
  (ProtocolOperationSite "UploadServer" (BlockId "server.proceed") 1)
  (Map.fromList
    [ ("payload", ProtocolSuccessor serverEp5)
    , ("cancel", ProtocolTerminal "cancelled")
    ])
  "phase0.endpoint.typestate.payload-choice.v1"

receivePayloadTransition :: ProtocolTransitionBinding
receivePayloadTransition = ProtocolTransitionBinding
  { protocolTransitionKey = ProtocolTransitionKey "upload.server.receive-payload"
  , protocolTransitionPredecessor = serverEp5
  , protocolTransitionAction = ProtocolReceiveExact
  , protocolTransitionTargetSite = ProtocolTerminatorSite
      "UploadServer" (BlockId "server.payload")
  , protocolTransitionTransport = uploadServerTransport
  , protocolTransitionOutcomes = Map.fromList
      [ ("success", ProtocolSuccessor serverEp6)
      , ("failure", ProtocolTerminal "EarlyEOF")
      ]
  , protocolTransitionBasis = CheckedProtocolCorrespondence
      "phase0.endpoint.typestate.payload-receive.v1"
  }

opaqueTransition
  :: Text
  -> EndpointOccurrenceKey
  -> ProtocolTargetSite
  -> Map.Map Text ProtocolTransitionOutcome
  -> Text
  -> ProtocolTransitionBinding
opaqueTransition key predecessor site outcomes evidence = ProtocolTransitionBinding
  { protocolTransitionKey = ProtocolTransitionKey key
  , protocolTransitionPredecessor = predecessor
  , protocolTransitionAction = ProtocolOpaqueAction key
  , protocolTransitionTargetSite = site
  , protocolTransitionTransport = uploadServerTransport
  , protocolTransitionOutcomes = outcomes
  , protocolTransitionBasis = CheckedLegacyOpaqueProtocolBridge evidence
  }
