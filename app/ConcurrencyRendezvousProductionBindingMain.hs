{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.ConcurrencyRendezvousCertification
import Phil.Core.Context (ResourceContext)
import Phil.Core.Generic
  ( GenericStaticParameterKey (..)
  , strictGenericInstantiationPolicy
  )
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
  { fixtureActivation :: CertifiedRendezvousActivation
  , fixtureProtocol :: CertifiedRendezvousProtocol
  , fixtureContexts :: Map.Map ProcessKey ProtocolContext
  , fixtureRequest :: ProcessRendezvousRequest
  , fixtureTransfer :: RestrictedMessageTransfer
  , fixtureEvidence :: RendezvousMessageEvidence
  , fixtureClientProcess :: ProcessKey
  , fixtureServerProcess :: ProcessKey
  }

main :: IO ()
main = do
  results <- sequence
    [ test "certified restricted rendezvous accepts exact production composition"
        certifiedRestrictedRendezvousAccepts
    , test "native missing-owner diagnostic precedes rendezvous kernel"
        nativeMissingOwnerPrecedence
    , test "independent Message evidence remains fail-closed"
        invalidMessageEvidenceRejects
    , test "endpoint kernel disagreement fails closed"
        endpointKernelDisagreementRejects
    , test "participant kernel disagreement fails closed"
        participantKernelDisagreementRejects
    , test "Message/coarse kernel disagreement fails closed"
        messageKernelDisagreementRejects
    , test "outer exact-rendezvous kernel disagreement fails closed"
        outerKernelDisagreementRejects
    , test "certified rendezvous emits only synchronous semantic causality"
        certifiedCausalityIsRendezvous
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

certifiedRestrictedRendezvousAccepts :: Either String ()
certifiedRestrictedRendezvousAccepts = do
  fx <- fixture
  result <- mapLeft show $ certifyRestrictedProcessRendezvous
    (fixtureActivation fx)
    (fixtureProtocol fx)
    (fixtureContexts fx)
    (fixtureRequest fx)
    (fixtureTransfer fx)
    (fixtureEvidence fx)
  let state = certifiedRendezvousState result
  assert
    (Map.lookup payloadOccurrence (communicationRestrictedOwners state)
      == Just (fixtureServerProcess fx, receivedPayload))
    "certified rendezvous did not preserve exact transferred occurrence identity"

nativeMissingOwnerPrecedence :: Either String ()
nativeMissingOwnerPrecedence = do
  fx <- fixture
  let fabricated = (fixtureTransfer fx)
        { restrictedMessageOccurrence = ActivationOccurrenceKey "fabricated.payload" }
  case certifyRestrictedProcessRendezvous
      (fixtureActivation fx)
      (fixtureProtocol fx)
      (fixtureContexts fx)
      (fixtureRequest fx)
      fabricated
      (fixtureEvidence fx) of
    Left (ConcurrencyRendezvousNativeError (RestrictedMessageOwnerUnknown key)) ->
      assert (key == ActivationOccurrenceKey "fabricated.payload")
        "native missing-owner diagnostic lost exact occurrence identity"
    other -> Left ("missing owner did not preserve native precedence: " <> show other)

invalidMessageEvidenceRejects :: Either String ()
invalidMessageEvidenceRejects = do
  fx <- fixture
  let evidence = fixtureEvidence fx
      badContract = (rendezvousMessageEvidenceContract evidence)
        { boundaryMessageContractRevision = "" }
      badEvidence = evidence { rendezvousMessageEvidenceContract = badContract }
  case certifyRestrictedProcessRendezvous
      (fixtureActivation fx)
      (fixtureProtocol fx)
      (fixtureContexts fx)
      (fixtureRequest fx)
      (fixtureTransfer fx)
      badEvidence of
    Left (ConcurrencyRendezvousMessageError BoundaryMessageContractRevisionEmpty) -> Right ()
    other -> Left ("invalid Message evidence was not rejected: " <> show other)

endpointKernelDisagreementRejects :: Either String ()
endpointKernelDisagreementRejects =
  case verifyRendezvousEndpointKernelFacts
      (allEndpointFacts { rendezvousSenderRoleExact = False }) of
    Left (ConcurrencyRendezvousEndpointKernelDisagreement facts) ->
      assert (not (rendezvousSenderRoleExact facts))
        "endpoint disagreement lost reflected sender-role fact"
    other -> Left ("endpoint disagreement did not fail closed: " <> show other)

participantKernelDisagreementRejects :: Either String ()
participantKernelDisagreementRejects =
  case verifyRendezvousParticipantKernelFacts
      (allParticipantFacts { rendezvousReceiverParticipantExact = False }) of
    Left (ConcurrencyRendezvousParticipantKernelDisagreement facts) ->
      assert (not (rendezvousReceiverParticipantExact facts))
        "participant disagreement lost reflected receiver fact"
    other -> Left ("participant disagreement did not fail closed: " <> show other)

messageKernelDisagreementRejects :: Either String ()
messageKernelDisagreementRejects =
  case verifyRendezvousMessageCoarseKernelFacts
      (allMessageFacts { rendezvousCoarseStepValid = False }) of
    Left (ConcurrencyRendezvousMessageCoarseKernelDisagreement facts) ->
      assert (not (rendezvousCoarseStepValid facts))
        "Message/coarse disagreement lost reflected step fact"
    other -> Left ("Message/coarse disagreement did not fail closed: " <> show other)

outerKernelDisagreementRejects :: Either String ()
outerKernelDisagreementRejects =
  case verifyExactInternalRendezvousKernelFacts True False True of
    Left (ConcurrencyRendezvousCertifiedKernelDisagreement True False True) -> Right ()
    other -> Left ("outer rendezvous disagreement did not fail closed: " <> show other)

certifiedCausalityIsRendezvous :: Either String ()
certifiedCausalityIsRendezvous = do
  fx <- fixture
  result <- mapLeft show $ certifyRestrictedProcessRendezvous
    (fixtureActivation fx)
    (fixtureProtocol fx)
    (fixtureContexts fx)
    (fixtureRequest fx)
    (fixtureTransfer fx)
    (fixtureEvidence fx)
  case certifiedRendezvousEventKind (certifiedRendezvousCausality result) of
    SynchronousRendezvousEvent sender receiver ->
      assert
        (sender == fixtureClientProcess fx && receiver == fixtureServerProcess fx)
        "certified causal witness changed exact sender/receiver ProcessKeys"
    other -> Left ("certified rendezvous emitted non-rendezvous causality: " <> show other)

allEndpointFacts :: RendezvousEndpointKernelFacts
allEndpointFacts = RendezvousEndpointKernelFacts
  True True True True True True True True True

allParticipantFacts :: RendezvousParticipantKernelFacts
allParticipantFacts = RendezvousParticipantKernelFacts True True True True True

allMessageFacts :: RendezvousMessageCoarseKernelFacts
allMessageFacts = RendezvousMessageCoarseKernelFacts True True True True True True True

fixture :: Either String Fixture
fixture = do
  protocol <- mapLeft show $ certifyRendezvousProtocol
    strictGenericInstantiationPolicy transferFamily [payloadArgument] []
  let instanceValue = certifiedRendezvousProtocolInstance protocol
      exactInstance = binaryProtocolInstanceRevision instanceValue
  graph <- mapLeft show rootGraph
  unactivated <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  let (clientProcess, serverProcess) = processKeys unactivated
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  let clientSession = protocolProjectionSession clientProjection
      serverSession = protocolProjectionSession serverProjection
      clientBindings =
        [ activationBinding
            clientEndpointOccurrence clientEndpoint Linear (TyEndpoint clientSession)
            (ProtocolEndpointOrigin "protocol.conc.rendezvous.client")
        , activationBinding
            payloadOccurrence payloadOwner Linear payloadTy
            (TargetParameterOrigin "client.payload")
        ]
      serverBindings =
        [ activationBinding
            serverEndpointOccurrence serverEndpoint Linear (TyEndpoint serverSession)
            (ProtocolEndpointOrigin "protocol.conc.rendezvous.server")
        ]
      contracts =
        [ ProcessActivationContract clientProcess clientBindings
        , ProcessActivationContract serverProcess serverBindings
        ]
      clientOccurrence = ProtocolRoleOccurrence exactInstance clientRole
      serverOccurrence = ProtocolRoleOccurrence exactInstance serverRole
      declarations =
        [ ParticipantDeclaration clientOccurrence (InternalParticipantTarget targetA)
        , ParticipantDeclaration serverOccurrence (InternalParticipantTarget targetB)
        ]
  activation <- mapLeft show $ certifyRendezvousActivation
    graph unactivated contracts [clientOccurrence, serverOccurrence] declarations
  clientResources <- requireResourceContext clientProcess
    (activationProcessContexts (certifiedRendezvousActivationState activation))
  serverResources <- requireResourceContext serverProcess
    (activationProcessContexts (certifiedRendezvousActivationState activation))
  let clientContext = ProtocolContext
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
      contexts = Map.fromList
        [ (clientProcess, clientContext)
        , (serverProcess, serverContext)
        ]
      request = exactRequest instanceValue clientProcess serverProcess
      transfer = RestrictedMessageTransfer
        { restrictedMessageOccurrence = payloadOccurrence
        , restrictedMessageSenderName = payloadOwner
        , restrictedMessageReceiverName = receivedPayload
        , restrictedMessageMode = Linear
        , restrictedMessageType = payloadTy
        }
  pure Fixture
    { fixtureActivation = activation
    , fixtureProtocol = protocol
    , fixtureContexts = contexts
    , fixtureRequest = request
    , fixtureTransfer = transfer
    , fixtureEvidence = rendezvousMessageEvidenceFromArgument payloadArgument
    , fixtureClientProcess = clientProcess
    , fixtureServerProcess = serverProcess
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

transferFamily :: BinaryProtocolFamily
transferFamily = BinaryProtocolFamily
  { protocolFamilyDeclarationKey = DeclarationKey "protocol.conc.rendezvous.production"
  , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.conc.rendezvous.production.v1"
  , protocolFamilyRequirements = Set.empty
  , protocolFamilyPrimaryRole = clientRole
  , protocolFamilyPeerRole = serverRole
  , protocolFamilyPrimarySession = ProtocolTemplateSend
      receivedPayload
      (ProtocolParameterType payloadParameter)
      (ProtocolTemplateEnd doneOutcome)
  }

payloadParameter :: GenericStaticParameterKey
payloadParameter = GenericStaticParameterKey "Payload"

payloadArgument :: ProtocolMessageArgument
payloadArgument = ProtocolMessageArgument
  { protocolMessageArgumentKey = payloadParameter
  , protocolMessageArgumentType = payloadTy
  , protocolMessageArgumentSemantics = payloadMessageSemantics
  , protocolMessageArgumentBoundaryContract = BoundaryMessageContract
      { boundaryMessageContractRevision = "boundary.message.conc.rendezvous.production.v1"
      , boundaryMessageContractType = payloadTy
      , boundaryMessageContractSemantics = payloadMessageSemantics
      , boundaryMessageContractShape = BoundaryMessageAdmittedLeaf "owned-restricted-message"
      }
  }

payloadMessageSemantics :: SemanticForm
payloadMessageSemantics = SemanticAtom "message.conc.rendezvous.production.payload"

exactRequest
  :: BinaryProtocolInstance
  -> ProcessKey
  -> ProcessKey
  -> ProcessRendezvousRequest
exactRequest instanceValue clientProcess serverProcess =
  let exactInstance = binaryProtocolInstanceRevision instanceValue
  in SendReceiveRendezvous
      ProcessRendezvousSide
        { rendezvousProcess = clientProcess
        , rendezvousEndpoint = clientEndpoint
        , rendezvousSuccessor = clientSuccessor
        , rendezvousInstance = exactInstance
        , rendezvousRole = clientRole
        }
      ProcessRendezvousSide
        { rendezvousProcess = serverProcess
        , rendezvousEndpoint = serverEndpoint
        , rendezvousSuccessor = serverSuccessor
        , rendezvousInstance = exactInstance
        , rendezvousRole = serverRole
        }

requireResourceContext
  :: ProcessKey
  -> Map.Map ProcessKey ResourceContext
  -> Either String ResourceContext
requireResourceContext processKey contexts =
  maybe (Left "missing process resource context") Right (Map.lookup processKey contexts)

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

clientEndpoint, serverEndpoint, clientSuccessor, serverSuccessor :: Name
clientEndpoint = Name "client.ep"
serverEndpoint = Name "server.ep"
clientSuccessor = Name "client.ep.next"
serverSuccessor = Name "server.ep.next"

payloadOwner, receivedPayload :: Name
payloadOwner = Name "payload-owner"
receivedPayload = Name "received-payload"

payloadTy :: Ty
payloadTy = TyOpaque "OwnedPayload"

doneOutcome :: Outcome
doneOutcome = Outcome "done"

payloadOccurrence, clientEndpointOccurrence, serverEndpointOccurrence :: ActivationOccurrenceKey
payloadOccurrence = ActivationOccurrenceKey "payload-occurrence"
clientEndpointOccurrence = ActivationOccurrenceKey "client-endpoint-occurrence"
serverEndpointOccurrence = ActivationOccurrenceKey "server-endpoint-occurrence"

siteA, siteB :: ProcessDeclarationSite
siteA = ProcessDeclarationSite (ProcessSiteKey "site-a") targetA
siteB = ProcessDeclarationSite (ProcessSiteKey "site-b") targetB

rootKey, targetA, targetB :: InstanceKey
rootKey = InstanceKey "root-instance"
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

slotA, slotB :: OccurrenceSlotKey
slotA = OccurrenceSlotKey "worker-a"
slotB = OccurrenceSlotKey "worker-b"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
