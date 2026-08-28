{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Context
  ( CheckError (DuplicateBinding)
  , ResourceContext (..)
  , insertBinding
  )
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-005 linear payload owner transfers exactly once" exactLinearTransferAccepted
    , test "CONC-005 stale sender reuse rejects" staleSenderReuseRejects
    , test "CONC-005 receiver duplication rejects" receiverDuplicationRejects
    , test "CONC-005 owner manufacture without exact occurrence rejects" ownerManufactureRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactLinearTransferAccepted :: Either String ()
exactLinearTransferAccepted = do
  (instanceValue, network, state, request, transfer, clientProcess, serverProcess) <- fixture
  updated <- mapLeft show $
    checkRestrictedProcessRendezvous instanceValue network state request transfer
  clientContext <- requireProtocolContext clientProcess (communicationProtocolContexts updated)
  serverContext <- requireProtocolContext serverProcess (communicationProtocolContexts updated)
  assert
    (Map.notMember payloadOwner (linearBindings (protocolResources clientContext)))
    "sender retained the transferred linear payload"
  assert
    (Map.lookup receivedPayload (linearBindings (protocolResources serverContext)) == Just payloadTy)
    "receiver did not obtain exactly one transferred linear payload"
  assert
    (Map.lookup payloadOccurrence (communicationRestrictedOwners updated)
      == Just (serverProcess, receivedPayload))
    "exact payload occurrence identity did not move sender -> receiver"
  assert
    (Map.lookup clientEndpointOccurrence (communicationRestrictedOwners updated)
      == Just (clientProcess, clientSuccessor))
    "client endpoint occurrence identity did not advance to successor"
  assert
    (Map.lookup serverEndpointOccurrence (communicationRestrictedOwners updated)
      == Just (serverProcess, serverSuccessor))
    "server endpoint occurrence identity did not advance to successor"

staleSenderReuseRejects :: Either String ()
staleSenderReuseRejects = do
  (instanceValue, network, state, request, transfer, _, serverProcess) <- fixture
  updated <- mapLeft show $
    checkRestrictedProcessRendezvous instanceValue network state request transfer
  case checkRestrictedProcessRendezvous instanceValue network updated request transfer of
    Left (RestrictedMessageOwnerMismatch key _ _ actualProcess actualName) ->
      assert
        ( key == payloadOccurrence
          && actualProcess == serverProcess
          && actualName == receivedPayload )
        "stale-sender rejection lost the current exact owner"
    other -> Left ("stale sender reused transferred owner: " <> show other)

receiverDuplicationRejects :: Either String ()
receiverDuplicationRejects = do
  (instanceValue, network, state, request, transfer, _, serverProcess) <- fixture
  serverContext <- requireProtocolContext serverProcess (communicationProtocolContexts state)
  duplicatedResources <- mapLeft show $
    insertBinding Linear receivedPayload payloadTy (protocolResources serverContext)
  let duplicatedServer = serverContext { protocolResources = duplicatedResources }
      duplicatedState = state
        { communicationProtocolContexts = Map.insert
            serverProcess duplicatedServer (communicationProtocolContexts state)
        }
  case checkRestrictedProcessRendezvous
      instanceValue network duplicatedState request transfer of
    Left (RestrictedMessageReceiverResourceError process (DuplicateBinding name)) ->
      assert
        (process == serverProcess && name == receivedPayload)
        "receiver-duplication rejection lost exact process/local name"
    other -> Left ("receiver duplication was not rejected: " <> show other)

ownerManufactureRejects :: Either String ()
ownerManufactureRejects = do
  (instanceValue, network, state, request, transfer, _, _) <- fixture
  let manufacturedState = state
        { communicationRestrictedOwners =
            Map.delete payloadOccurrence (communicationRestrictedOwners state)
        }
  case checkRestrictedProcessRendezvous
      instanceValue network manufacturedState request transfer of
    Left (RestrictedMessageOwnerUnknown key) ->
      assert (key == payloadOccurrence)
        "missing-owner rejection named the wrong occurrence"
    other -> Left ("payload owner was manufactured without exact identity: " <> show other)

fixture
  :: Either String
      ( BinaryProtocolInstance
      , ProcessNetwork
      , ProcessCommunicationState
      , ProcessRendezvousRequest
      , RestrictedMessageTransfer
      , ProcessKey
      , ProcessKey
      )
fixture = do
  instanceValue <- protocolInstance
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
            (ProtocolEndpointOrigin "protocol.conc005.client")
        , activationBinding
            payloadOccurrence payloadOwner Linear payloadTy
            (TargetParameterOrigin "client.payload")
        ]
      serverBindings =
        [ activationBinding
            serverEndpointOccurrence serverEndpoint Linear (TyEndpoint serverSession)
            (ProtocolEndpointOrigin "protocol.conc005.server")
        ]
  (network, activationState) <- mapLeft show $ activateProcessState unactivated
    [ ProcessActivationContract clientProcess clientBindings
    , ProcessActivationContract serverProcess serverBindings
    ]
  clientResources <- requireResourceContext clientProcess
    (activationProcessContexts activationState)
  serverResources <- requireResourceContext serverProcess
    (activationProcessContexts activationState)
  let exactInstance = binaryProtocolInstanceRevision instanceValue
      clientProtocolContext = ProtocolContext
        { protocolResources = clientResources
        , protocolEndpoints = Map.singleton clientEndpoint ProtocolEndpointBinding
            { protocolEndpointName = clientEndpoint
            , protocolEndpointInstance = exactInstance
            , protocolEndpointRole = clientRole
            , protocolEndpointSession = clientSession
            }
        }
      serverProtocolContext = ProtocolContext
        { protocolResources = serverResources
        , protocolEndpoints = Map.singleton serverEndpoint ProtocolEndpointBinding
            { protocolEndpointName = serverEndpoint
            , protocolEndpointInstance = exactInstance
            , protocolEndpointRole = serverRole
            , protocolEndpointSession = serverSession
            }
        }
      protocolContexts = Map.fromList
        [ (clientProcess, clientProtocolContext)
        , (serverProcess, serverProtocolContext)
        ]
  state <- mapLeft show $
    communicationStateFromActivation activationState protocolContexts
  let request = exactRequest instanceValue clientProcess serverProcess
      transfer = RestrictedMessageTransfer
        { restrictedMessageOccurrence = payloadOccurrence
        , restrictedMessageSenderName = payloadOwner
        , restrictedMessageReceiverName = receivedPayload
        , restrictedMessageMode = Linear
        , restrictedMessageType = payloadTy
        }
  pure
    ( instanceValue
    , network
    , state
    , request
    , transfer
    , clientProcess
    , serverProcess
    )

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
  , activationStartsSharedLoan = False
  }

protocolInstance :: Either String BinaryProtocolInstance
protocolInstance = mapLeft show $ instantiateBinaryProtocol
  strictGenericInstantiationPolicy
  transferFamily
  []
  []

transferFamily :: BinaryProtocolFamily
transferFamily = BinaryProtocolFamily
  { protocolFamilyDeclarationKey = DeclarationKey "protocol.conc005"
  , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.conc005.v1"
  , protocolFamilyRequirements = Set.empty
  , protocolFamilyPrimaryRole = clientRole
  , protocolFamilyPeerRole = serverRole
  , protocolFamilyPrimarySession = ProtocolTemplateSend
      receivedPayload
      (ProtocolConcreteType payloadTy)
      (ProtocolTemplateEnd doneOutcome)
  }

exactRequest
  :: BinaryProtocolInstance
  -> ProcessKey
  -> ProcessKey
  -> ProcessRendezvousRequest
exactRequest instanceValue clientProcess serverProcess =
  let exactInstance = binaryProtocolInstanceRevision instanceValue
      clientSide = ProcessRendezvousSide
        { rendezvousProcess = clientProcess
        , rendezvousEndpoint = clientEndpoint
        , rendezvousSuccessor = clientSuccessor
        , rendezvousInstance = exactInstance
        , rendezvousRole = clientRole
        }
      serverSide = ProcessRendezvousSide
        { rendezvousProcess = serverProcess
        , rendezvousEndpoint = serverEndpoint
        , rendezvousSuccessor = serverSuccessor
        , rendezvousInstance = exactInstance
        , rendezvousRole = serverRole
        }
  in SendReceiveRendezvous clientSide serverSide

requireProtocolContext
  :: ProcessKey
  -> Map.Map ProcessKey ProtocolContext
  -> Either String ProtocolContext
requireProtocolContext processKey contexts =
  maybe (Left "missing process protocol context") Right (Map.lookup processKey contexts)

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
