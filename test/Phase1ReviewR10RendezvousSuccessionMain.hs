{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode
import Phil.Core.ConcurrencyRendezvousCertification
import Phil.Core.Context (ResourceContext)
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
  { fixtureActivation :: CertifiedRendezvousActivation
  , fixtureProtocol :: CertifiedRendezvousProtocol
  , fixtureContexts :: Map.Map ProcessKey ProtocolContext
  , fixtureFirstRequest :: ProcessRendezvousRequest
  , fixtureReplyRequest :: ProcessRendezvousRequest
  , fixtureEvidence :: RendezvousMessageEvidence
  , fixtureClientProcess :: ProcessKey
  , fixtureServerProcess :: ProcessKey
  }

main :: IO ()
main = do
  results <- sequence
    [ test "REVIEW-R10 certified request/reply composes through exact successor"
        requestReplyComposes
    , test "REVIEW-R10 stale predecessor endpoint names reject on successor path"
        stalePredecessorRejects
    , test "REVIEW-R10 activation-only checker remains strict on live successor"
        activationOnlyPathRemainsStrict
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

requestReplyComposes :: Either String ()
requestReplyComposes = do
  fx <- fixture
  first <- mapLeft show $ certifyProcessRendezvous
    (fixtureActivation fx)
    (fixtureProtocol fx)
    (fixtureContexts fx)
    (fixtureFirstRequest fx)
    (fixtureEvidence fx)
  second <- mapLeft show $ certifyProcessRendezvousSuccessor
    (fixtureActivation fx)
    (fixtureProtocol fx)
    first
    (fixtureReplyRequest fx)
    (fixtureEvidence fx)
  let contexts = communicationProtocolContexts (certifiedRendezvousState second)
  clientContext <- requireProtocolContext (fixtureClientProcess fx) contexts
  serverContext <- requireProtocolContext (fixtureServerProcess fx) contexts
  assert
    (lookupProtocolEndpoint clientSecondSuccessor clientContext /= Nothing)
    "request/reply chain did not preserve the client's exact second successor"
  assert
    (lookupProtocolEndpoint serverSecondSuccessor serverContext /= Nothing)
    "request/reply chain did not preserve the server's exact second successor"
  case certifiedRendezvousEventKind (certifiedRendezvousCausality second) of
    SynchronousRendezvousEvent sender receiver ->
      assert
        (sender == fixtureServerProcess fx && receiver == fixtureClientProcess fx)
        "reply rendezvous did not preserve opposite sender/receiver direction"
    other -> Left ("reply emitted non-rendezvous causality: " <> show other)

stalePredecessorRejects :: Either String ()
stalePredecessorRejects = do
  fx <- fixture
  first <- mapLeft show $ certifyProcessRendezvous
    (fixtureActivation fx)
    (fixtureProtocol fx)
    (fixtureContexts fx)
    (fixtureFirstRequest fx)
    (fixtureEvidence fx)
  case certifyProcessRendezvousSuccessor
      (fixtureActivation fx)
      (fixtureProtocol fx)
      first
      (fixtureFirstRequest fx)
      (fixtureEvidence fx) of
    Left (ConcurrencyRendezvousNativeError
      (RendezvousEndpointNotOwnedByProcess processKey endpoint)) ->
        assert
          (processKey == fixtureClientProcess fx && endpoint == clientEndpoint)
          "stale-predecessor rejection lost exact process/endpoint identity"
    other -> Left ("stale predecessor endpoint names were accepted: " <> show other)

activationOnlyPathRemainsStrict :: Either String ()
activationOnlyPathRemainsStrict = do
  fx <- fixture
  first <- mapLeft show $ certifyProcessRendezvous
    (fixtureActivation fx)
    (fixtureProtocol fx)
    (fixtureContexts fx)
    (fixtureFirstRequest fx)
    (fixtureEvidence fx)
  let contexts = communicationProtocolContexts (certifiedRendezvousState first)
      instanceValue = certifiedRendezvousProtocolInstance (fixtureProtocol fx)
      network = certifiedRendezvousActivationNetwork (fixtureActivation fx)
  case checkProcessCommunication
      instanceValue network contexts
      (JointProcessRendezvous (fixtureReplyRequest fx)) of
    Left (RendezvousProjectionSessionMismatch processKey _ _) ->
      assert (processKey == fixtureServerProcess fx)
        "activation-only projection mismatch named the wrong live sender"
    other -> Left ("activation-only path stopped enforcing initial projection: " <> show other)

fixture :: Either String Fixture
fixture = do
  protocol <- mapLeft show $ certifyRendezvousProtocol
    strictGenericInstantiationPolicy requestReplyFamily [unitArgument] []
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
            (ProtocolEndpointOrigin "protocol.review.r10.client")
        ]
      serverBindings =
        [ activationBinding
            serverEndpointOccurrence serverEndpoint Linear (TyEndpoint serverSession)
            (ProtocolEndpointOrigin "protocol.review.r10.server")
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
      firstRequest = SendReceiveRendezvous
        (side clientProcess clientEndpoint clientFirstSuccessor clientRole exactInstance)
        (side serverProcess serverEndpoint serverFirstSuccessor serverRole exactInstance)
      replyRequest = SendReceiveRendezvous
        (side serverProcess serverFirstSuccessor serverSecondSuccessor serverRole exactInstance)
        (side clientProcess clientFirstSuccessor clientSecondSuccessor clientRole exactInstance)
  pure Fixture
    { fixtureActivation = activation
    , fixtureProtocol = protocol
    , fixtureContexts = contexts
    , fixtureFirstRequest = firstRequest
    , fixtureReplyRequest = replyRequest
    , fixtureEvidence = rendezvousMessageEvidenceFromArgument unitArgument
    , fixtureClientProcess = clientProcess
    , fixtureServerProcess = serverProcess
    }

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

requestReplyFamily :: BinaryProtocolFamily
requestReplyFamily = BinaryProtocolFamily
  { protocolFamilyDeclarationKey = DeclarationKey "protocol.review.r10.request-reply"
  , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.review.r10.request-reply.v1"
  , protocolFamilyRequirements = Set.empty
  , protocolFamilyPrimaryRole = clientRole
  , protocolFamilyPeerRole = serverRole
  , protocolFamilyPrimarySession = ProtocolTemplateSend
      (Name "request")
      (ProtocolParameterType unitParameter)
      (ProtocolTemplateReceive
        (Name "reply")
        (ProtocolParameterType unitParameter)
        (ProtocolTemplateEnd (Outcome "done")))
  }

unitParameter :: GenericStaticParameterKey
unitParameter = GenericStaticParameterKey "Payload"

unitArgument :: ProtocolMessageArgument
unitArgument = ProtocolMessageArgument
  { protocolMessageArgumentKey = unitParameter
  , protocolMessageArgumentType = TyUnit
  , protocolMessageArgumentSemantics = SemanticAtom "message.review.r10.unit"
  , protocolMessageArgumentBoundaryContract = BoundaryMessageContract
      { boundaryMessageContractRevision = "boundary.message.review.r10.unit.v1"
      , boundaryMessageContractType = TyUnit
      , boundaryMessageContractSemantics = SemanticAtom "message.review.r10.unit"
      , boundaryMessageContractShape = BoundaryMessageAdmittedLeaf "unit-request-reply"
      }
  }

requireResourceContext
  :: ProcessKey
  -> Map.Map ProcessKey ResourceContext
  -> Either String ResourceContext
requireResourceContext processKey contexts =
  maybe (Left "missing process resource context") Right (Map.lookup processKey contexts)

requireProtocolContext
  :: ProcessKey
  -> Map.Map ProcessKey ProtocolContext
  -> Either String ProtocolContext
requireProtocolContext processKey contexts =
  maybe (Left "missing process protocol context") Right (Map.lookup processKey contexts)

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

clientEndpointOccurrence, serverEndpointOccurrence :: ActivationOccurrenceKey
clientEndpointOccurrence = ActivationOccurrenceKey "review-r10-client-endpoint"
serverEndpointOccurrence = ActivationOccurrenceKey "review-r10-server-endpoint"

siteA, siteB :: ProcessDeclarationSite
siteA = ProcessDeclarationSite (ProcessSiteKey "review-r10-site-a") targetA
siteB = ProcessDeclarationSite (ProcessSiteKey "review-r10-site-b") targetB

rootKey, targetA, targetB :: InstanceKey
rootKey = InstanceKey "review-r10-root-instance"
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

slotA, slotB :: OccurrenceSlotKey
slotA = OccurrenceSlotKey "review-r10-worker-a"
slotB = OccurrenceSlotKey "review-r10-worker-b"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
