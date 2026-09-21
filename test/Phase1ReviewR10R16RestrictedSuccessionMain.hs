{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode
import Phil.Core.ConcurrencyRendezvousCertification
import Phil.Core.ConcurrencyTerminalCertification
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Generic
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessCausality (ProcessEventKind (..))
import Phil.Core.ProcessParticipants
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Protocol.MessageAdmissibility
import Phil.Core.Static
import Phil.Core.Syntax
import System.Exit (exitFailure)

data Fixture = Fixture
  { fixtureActivationA :: CertifiedRendezvousActivation
  , fixtureActivationB :: CertifiedRendezvousActivation
  , fixtureProtocol :: CertifiedRendezvousProtocol
  , fixtureContextsA :: Map.Map ProcessKey ProtocolContext
  , fixtureContextsB :: Map.Map ProcessKey ProtocolContext
  , fixtureFirstRequest :: ProcessRendezvousRequest
  , fixtureReplyRequest :: ProcessRendezvousRequest
  , fixtureFirstTransfer :: RestrictedMessageTransfer
  , fixtureReplyTransfer :: RestrictedMessageTransfer
  , fixtureEvidence :: RendezvousMessageEvidence
  , fixtureClientProcess :: ProcessKey
  , fixtureServerProcess :: ProcessKey
  }

main :: IO ()
main = do
  results <- sequence
    [ test "R10 restricted request/reply composes through exact live successor"
        restrictedRequestReplyComposes
    , test "R10 unrestricted successor cannot bypass a required restricted transfer"
        missingTransferRejects
    , test "R10 restricted successor rejects stale endpoint names"
        staleEndpointRejects
    , test "R16 unrestricted successor rejects a donor activation"
        unrestrictedDonorActivationRejects
    , test "R16 restricted successor rejects a donor activation"
        restrictedDonorActivationRejects
    , test "R16 donor activation preserves its own extra owner on its own chain"
        donorActivationPositiveControl
    , test "R16 terminal enabled-rendezvous bridge rejects donor lineage"
        terminalBridgeRejectsDonor
    , test "R10 initial restricted admission remains strict on advanced contexts"
        initialRestrictedPathRemainsStrict
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

restrictedRequestReplyComposes :: Either String ()
restrictedRequestReplyComposes = do
  fx <- fixture
  first <- firstUnder (fixtureActivationA fx) (fixtureContextsA fx) fx
  second <- mapLeft show $ certifyRestrictedProcessRendezvousSuccessor
    (fixtureActivationA fx)
    (fixtureProtocol fx)
    first
    (fixtureReplyRequest fx)
    (fixtureReplyTransfer fx)
    (fixtureEvidence fx)
  let state = certifiedRendezvousState second
      owners = communicationRestrictedOwners state
      contexts = communicationProtocolContexts state
  assert
    (Map.lookup payloadOccurrence owners
      == Just (fixtureClientProcess fx, payloadClient2))
    "restricted reply did not return the exact payload occurrence to the client"
  assert
    (Map.lookup clientEndpointOccurrence owners
      == Just (fixtureClientProcess fx, clientSecondSuccessor))
    "restricted reply did not advance the client endpoint owner twice"
  assert
    (Map.lookup serverEndpointOccurrence owners
      == Just (fixtureServerProcess fx, serverSecondSuccessor))
    "restricted reply did not advance the server endpoint owner twice"
  client <- requireProtocolContext (fixtureClientProcess fx) contexts
  server <- requireProtocolContext (fixtureServerProcess fx) contexts
  assert
    (Map.lookup payloadClient2 (linearBindings (protocolResources client)) == Just payloadTy)
    "client did not receive the returned linear payload"
  assert
    (Map.notMember payloadServer1 (linearBindings (protocolResources server)))
    "server retained the returned linear payload"
  case certifiedRendezvousEventKind (certifiedRendezvousCausality second) of
    SynchronousRendezvousEvent sender receiver ->
      assert
        (sender == fixtureServerProcess fx && receiver == fixtureClientProcess fx)
        "restricted reply lost opposite-direction causality"
    other -> Left ("restricted reply emitted non-rendezvous causality: " <> show other)

missingTransferRejects :: Either String ()
missingTransferRejects = do
  fx <- fixture
  first <- firstUnder (fixtureActivationA fx) (fixtureContextsA fx) fx
  case certifyProcessRendezvousSuccessor
      (fixtureActivationA fx)
      (fixtureProtocol fx)
      first
      (fixtureReplyRequest fx)
      (fixtureEvidence fx) of
    Left (ConcurrencyRendezvousMessageTransferRequired actual) ->
      assert (actual == payloadTy) "missing-transfer rejection reported the wrong message type"
    other -> Left ("restricted reply escaped through transfer-free successor: " <> show other)

staleEndpointRejects :: Either String ()
staleEndpointRejects = do
  fx <- fixture
  first <- firstUnder (fixtureActivationA fx) (fixtureContextsA fx) fx
  let staleReply = SendReceiveRendezvous
        (side (fixtureServerProcess fx) serverEndpoint serverSecondSuccessor serverRole exactInstance)
        (side (fixtureClientProcess fx) clientFirstSuccessor clientSecondSuccessor clientRole exactInstance)
      exactInstance = binaryProtocolInstanceRevision
        (certifiedRendezvousProtocolInstance (fixtureProtocol fx))
  case certifyRestrictedProcessRendezvousSuccessor
      (fixtureActivationA fx)
      (fixtureProtocol fx)
      first
      staleReply
      (fixtureReplyTransfer fx)
      (fixtureEvidence fx) of
    Left (ConcurrencyRendezvousNativeError
      (RendezvousEndpointNotOwnedByProcess process name)) ->
        assert (process == fixtureServerProcess fx && name == serverEndpoint)
          "stale restricted endpoint rejection lost exact server/name identity"
    other -> Left ("stale restricted successor endpoint was accepted: " <> show other)

unrestrictedDonorActivationRejects :: Either String ()
unrestrictedDonorActivationRejects = do
  fx <- fixture
  first <- firstUnder (fixtureActivationA fx) (fixtureContextsA fx) fx
  case certifyProcessRendezvousSuccessor
      (fixtureActivationB fx)
      (fixtureProtocol fx)
      first
      (fixtureReplyRequest fx)
      (fixtureEvidence fx) of
    Left ConcurrencyRendezvousActivationLineageMismatch -> Right ()
    other -> Left ("unrestricted successor accepted donor activation: " <> show other)

restrictedDonorActivationRejects :: Either String ()
restrictedDonorActivationRejects = do
  fx <- fixture
  first <- firstUnder (fixtureActivationA fx) (fixtureContextsA fx) fx
  case certifyRestrictedProcessRendezvousSuccessor
      (fixtureActivationB fx)
      (fixtureProtocol fx)
      first
      (fixtureReplyRequest fx)
      (fixtureReplyTransfer fx)
      (fixtureEvidence fx) of
    Left ConcurrencyRendezvousActivationLineageMismatch -> Right ()
    other -> Left ("restricted successor accepted donor activation: " <> show other)

donorActivationPositiveControl :: Either String ()
donorActivationPositiveControl = do
  fx <- fixture
  first <- firstUnder (fixtureActivationB fx) (fixtureContextsB fx) fx
  second <- mapLeft show $ certifyRestrictedProcessRendezvousSuccessor
    (fixtureActivationB fx)
    (fixtureProtocol fx)
    first
    (fixtureReplyRequest fx)
    (fixtureReplyTransfer fx)
    (fixtureEvidence fx)
  let owners = communicationRestrictedOwners (certifiedRendezvousState second)
  assert
    (Map.lookup extraOccurrence owners
      == Just (fixtureClientProcess fx, extraOwner))
    "donor activation's genuine extra owner was lost on its own successor chain"
  assert
    (Map.lookup payloadOccurrence owners
      == Just (fixtureClientProcess fx, payloadClient2))
    "donor activation's payload did not complete the same request/reply chain"

terminalBridgeRejectsDonor :: Either String ()
terminalBridgeRejectsDonor = do
  fx <- fixture
  runtime <- mapLeft show $ initializeCertifiedTerminalRuntime
    (fixtureActivationA fx) (fixtureContextsA fx) Map.empty
  donorStep <- firstUnder (fixtureActivationB fx) (fixtureContextsB fx) fx
  case certifyEnabledRendezvousStep runtime donorStep of
    Left ConcurrencyTerminalRendezvousActivationLineageMismatch -> Right ()
    other -> Left ("terminal bridge accepted donor rendezvous lineage: " <> show other)

initialRestrictedPathRemainsStrict :: Either String ()
initialRestrictedPathRemainsStrict = do
  fx <- fixture
  first <- firstUnder (fixtureActivationA fx) (fixtureContextsA fx) fx
  let liveContexts = communicationProtocolContexts (certifiedRendezvousState first)
  case certifyRestrictedProcessRendezvous
      (fixtureActivationA fx)
      (fixtureProtocol fx)
      liveContexts
      (fixtureReplyRequest fx)
      (fixtureReplyTransfer fx)
      (fixtureEvidence fx) of
    Left (ConcurrencyRendezvousNativeError
      (RendezvousActivationResourceMismatch process _ _)) ->
        assert
          (process == fixtureClientProcess fx || process == fixtureServerProcess fx)
          "initial restricted admission mismatch named an unrelated process"
    other -> Left ("initial restricted path accepted advanced live contexts: " <> show other)

firstUnder
  :: CertifiedRendezvousActivation
  -> Map.Map ProcessKey ProtocolContext
  -> Fixture
  -> Either String CertifiedRendezvousResult
firstUnder activation contexts fx = mapLeft show $ certifyRestrictedProcessRendezvous
  activation
  (fixtureProtocol fx)
  contexts
  (fixtureFirstRequest fx)
  (fixtureFirstTransfer fx)
  (fixtureEvidence fx)

fixture :: Either String Fixture
fixture = do
  protocol <- mapLeft show $ certifyRendezvousProtocol
    strictGenericInstantiationPolicy transferReplyFamily [payloadArgument] []
  let instanceValue = certifiedRendezvousProtocolInstance protocol
      exactInstance = binaryProtocolInstanceRevision instanceValue
  graph <- mapLeft show rootGraph
  unactivated <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  let (clientProcess, serverProcess) = processKeys unactivated
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  let clientSession = protocolProjectionSession clientProjection
      serverSession = protocolProjectionSession serverProjection
      clientEndpointBinding = activationBinding
        clientEndpointOccurrence clientEndpoint Linear (TyEndpoint clientSession)
        (ProtocolEndpointOrigin "protocol.review.r10-r16.client")
      serverEndpointBinding = activationBinding
        serverEndpointOccurrence serverEndpoint Linear (TyEndpoint serverSession)
        (ProtocolEndpointOrigin "protocol.review.r10-r16.server")
      payloadBinding = activationBinding
        payloadOccurrence payloadClient0 Linear payloadTy
        (TargetParameterOrigin "client.payload")
      extraBinding = activationBinding
        extraOccurrence extraOwner Linear payloadTy
        (TargetParameterOrigin "client.extra")
      contractsA =
        [ ProcessActivationContract clientProcess [clientEndpointBinding, payloadBinding]
        , ProcessActivationContract serverProcess [serverEndpointBinding]
        ]
      contractsB =
        [ ProcessActivationContract clientProcess [clientEndpointBinding, payloadBinding, extraBinding]
        , ProcessActivationContract serverProcess [serverEndpointBinding]
        ]
      clientOccurrence = ProtocolRoleOccurrence exactInstance clientRole
      serverOccurrence = ProtocolRoleOccurrence exactInstance serverRole
      declarations =
        [ ParticipantDeclaration clientOccurrence (InternalParticipantTarget targetA)
        , ParticipantDeclaration serverOccurrence (InternalParticipantTarget targetB)
        ]
  activationA <- mapLeft show $ certifyRendezvousActivation
    graph unactivated contractsA [clientOccurrence, serverOccurrence] declarations
  activationB <- mapLeft show $ certifyRendezvousActivation
    graph unactivated contractsB [clientOccurrence, serverOccurrence] declarations
  contextsA <- contextsFor activationA protocol clientProcess serverProcess
    clientSession serverSession
  contextsB <- contextsFor activationB protocol clientProcess serverProcess
    clientSession serverSession
  let firstRequest = SendReceiveRendezvous
        (side clientProcess clientEndpoint clientFirstSuccessor clientRole exactInstance)
        (side serverProcess serverEndpoint serverFirstSuccessor serverRole exactInstance)
      replyRequest = SendReceiveRendezvous
        (side serverProcess serverFirstSuccessor serverSecondSuccessor serverRole exactInstance)
        (side clientProcess clientFirstSuccessor clientSecondSuccessor clientRole exactInstance)
      firstTransfer = RestrictedMessageTransfer
        { restrictedMessageOccurrence = payloadOccurrence
        , restrictedMessageSenderName = payloadClient0
        , restrictedMessageReceiverName = payloadServer1
        , restrictedMessageMode = Linear
        , restrictedMessageType = payloadTy
        }
      replyTransfer = RestrictedMessageTransfer
        { restrictedMessageOccurrence = payloadOccurrence
        , restrictedMessageSenderName = payloadServer1
        , restrictedMessageReceiverName = payloadClient2
        , restrictedMessageMode = Linear
        , restrictedMessageType = payloadTy
        }
  pure Fixture
    { fixtureActivationA = activationA
    , fixtureActivationB = activationB
    , fixtureProtocol = protocol
    , fixtureContextsA = contextsA
    , fixtureContextsB = contextsB
    , fixtureFirstRequest = firstRequest
    , fixtureReplyRequest = replyRequest
    , fixtureFirstTransfer = firstTransfer
    , fixtureReplyTransfer = replyTransfer
    , fixtureEvidence = rendezvousMessageEvidenceFromArgument payloadArgument
    , fixtureClientProcess = clientProcess
    , fixtureServerProcess = serverProcess
    }

contextsFor
  :: CertifiedRendezvousActivation
  -> CertifiedRendezvousProtocol
  -> ProcessKey
  -> ProcessKey
  -> Session
  -> Session
  -> Either String (Map.Map ProcessKey ProtocolContext)
contextsFor activation protocol clientProcess serverProcess clientSession serverSession = do
  clientResources <- requireResourceContext clientProcess
    (activationProcessContexts (certifiedRendezvousActivationState activation))
  serverResources <- requireResourceContext serverProcess
    (activationProcessContexts (certifiedRendezvousActivationState activation))
  let exactInstance = binaryProtocolInstanceRevision
        (certifiedRendezvousProtocolInstance protocol)
      clientContext = ProtocolContext
        { protocolResources = clientResources
        , protocolEndpoints = Map.singleton clientEndpoint ProtocolEndpointBinding
            { protocolEndpointName = clientEndpoint
            , protocolEndpointInstance = exactInstance
            , protocolEndpointRole = clientRole
            , protocolEndpointSession = clientSession
            }
        }
      serverContext = ProtocolContext
        { protocolResources = serverResources
        , protocolEndpoints = Map.singleton serverEndpoint ProtocolEndpointBinding
            { protocolEndpointName = serverEndpoint
            , protocolEndpointInstance = exactInstance
            , protocolEndpointRole = serverRole
            , protocolEndpointSession = serverSession
            }
        }
  pure (Map.fromList [(clientProcess, clientContext), (serverProcess, serverContext)])

side
  :: ProcessKey
  -> Name
  -> Name
  -> ProtocolRoleKey
  -> ProtocolInstanceRevision
  -> ProcessRendezvousSide
side process predecessor successor role instanceRevision = ProcessRendezvousSide
  { rendezvousProcess = process
  , rendezvousEndpoint = predecessor
  , rendezvousSuccessor = successor
  , rendezvousInstance = instanceRevision
  , rendezvousRole = role
  }

activationBinding
  :: ActivationOccurrenceKey
  -> Name
  -> Mode
  -> Ty
  -> ActivationBindingOrigin
  -> ActivationBinding
activationBinding occurrence name mode ty origin = ActivationBinding
  { activationOccurrenceKey = occurrence
  , activationLocalName = name
  , activationCheckedTypeMode = CheckedTypeMode ty mode
  , activationBindingOrigin = origin
  , activationReachability = DirectStatefulReachability occurrence
  , activationStartsSharedLoan = False
  }

transferReplyFamily :: BinaryProtocolFamily
transferReplyFamily = BinaryProtocolFamily
  { protocolFamilyDeclarationKey = DeclarationKey "protocol.review.r10-r16.transfer-reply"
  , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.review.r10-r16.transfer-reply.v1"
  , protocolFamilyRequirements = Set.empty
  , protocolFamilyPrimaryRole = clientRole
  , protocolFamilyPeerRole = serverRole
  , protocolFamilyPrimarySession = ProtocolTemplateSend
      (Name "request")
      (ProtocolParameterType payloadParameter)
      (ProtocolTemplateReceive
        (Name "reply")
        (ProtocolParameterType payloadParameter)
        (ProtocolTemplateEnd (Outcome "done")))
  }

payloadParameter :: GenericStaticParameterKey
payloadParameter = GenericStaticParameterKey "Payload"

payloadArgument :: ProtocolMessageArgument
payloadArgument = ProtocolMessageArgument
  { protocolMessageArgumentKey = payloadParameter
  , protocolMessageArgumentType = payloadTy
  , protocolMessageArgumentSemantics = payloadSemantics
  , protocolMessageArgumentBoundaryContract = BoundaryMessageContract
      { boundaryMessageContractRevision = "boundary.message.review.r10-r16.payload.v1"
      , boundaryMessageContractType = payloadTy
      , boundaryMessageContractSemantics = payloadSemantics
      , boundaryMessageContractShape = BoundaryMessageAdmittedLeaf "linear-u8"
      }
  }

payloadTy :: Ty
payloadTy = TyUInt 8

payloadSemantics :: SemanticForm
payloadSemantics = SemanticAtom "message.review.r10-r16.payload"

requireProtocolContext
  :: ProcessKey -> Map.Map ProcessKey ProtocolContext -> Either String ProtocolContext
requireProtocolContext process contexts =
  maybe (Left "missing process protocol context") Right (Map.lookup process contexts)

requireResourceContext
  :: ProcessKey -> Map.Map ProcessKey ResourceContext -> Either String ResourceContext
requireResourceContext process contexts =
  maybe (Left "missing process resource context") Right (Map.lookup process contexts)

processKeys :: ProcessNetwork -> (ProcessKey, ProcessKey)
processKeys network =
  let rootRevision = identityInstanceRevision (processNetworkRoot network)
  in ( deriveProcessKey rootRevision (processSiteKey siteA)
     , deriveProcessKey rootRevision (processSiteKey siteB)
     )

rootGraph :: Either ArchitectureInstantiationError ArchitectureInstanceGraph
rootGraph = instantiateArchitecture rootKey rootSpec

rootSpec :: ArchitectureNodeSpec
rootSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "root"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren =
      [ ArchitectureChildSpec slotA workerSpec
      , ArchitectureChildSpec slotB workerSpec
      ]
  , architectureNodeReferences = []
  }

workerSpec :: ArchitectureNodeSpec
workerSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "worker"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

declaration :: Text -> DeclarationIdentity
declaration label = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation
      { declarationDisplayName = label
      , declarationModulePath = []
      }
  , declarationKey = DeclarationKey ("decl-" <> label)
  , declarationInterfaceSemantics = SemanticAtom "interface"
  , declarationDefinitionSemantics = SemanticAtom "definition"
  }

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "client"
serverRole = ProtocolRoleKey "server"

clientEndpoint, serverEndpoint, clientFirstSuccessor, serverFirstSuccessor :: Name
clientEndpoint = Name "client.ep"
serverEndpoint = Name "server.ep"
clientFirstSuccessor = Name "client.ep.1"
serverFirstSuccessor = Name "server.ep.1"

clientSecondSuccessor, serverSecondSuccessor :: Name
clientSecondSuccessor = Name "client.ep.2"
serverSecondSuccessor = Name "server.ep.2"

payloadClient0, payloadServer1, payloadClient2, extraOwner :: Name
payloadClient0 = Name "payload.client.0"
payloadServer1 = Name "payload.server.1"
payloadClient2 = Name "payload.client.2"
extraOwner = Name "activation-b.extra"

clientEndpointOccurrence, serverEndpointOccurrence, payloadOccurrence, extraOccurrence
  :: ActivationOccurrenceKey
clientEndpointOccurrence = ActivationOccurrenceKey "review-r10-r16-client-endpoint"
serverEndpointOccurrence = ActivationOccurrenceKey "review-r10-r16-server-endpoint"
payloadOccurrence = ActivationOccurrenceKey "review-r10-r16-payload"
extraOccurrence = ActivationOccurrenceKey "review-r10-r16-extra"

siteA, siteB :: ProcessDeclarationSite
siteA = ProcessDeclarationSite (ProcessSiteKey "review-r10-r16-site-a") targetA
siteB = ProcessDeclarationSite (ProcessSiteKey "review-r10-r16-site-b") targetB

rootKey, targetA, targetB :: InstanceKey
rootKey = InstanceKey "review-r10-r16-root-instance"
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

slotA, slotB :: OccurrenceSlotKey
slotA = OccurrenceSlotKey "review-r10-r16-worker-a"
slotB = OccurrenceSlotKey "review-r10-r16-worker-b"

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
