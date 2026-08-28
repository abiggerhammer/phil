{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Process
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-004 exact dual send/receive advances jointly" exactRendezvousAccepted
    , test "CONC-004 unilateral endpoint progression rejects" unilateralProgressRejects
    , test "CONC-004 equal-shape wrong protocol instance rejects" wrongInstanceRejects
    , test "CONC-004 wrong exact role rejects" wrongRoleRejects
    , test "CONC-004 endpoint bound to wrong process rejects" wrongProcessBindingRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactRendezvousAccepted :: Either String ()
exactRendezvousAccepted = do
  instanceValue <- protocolInstance
  network <- activeNetwork
  contexts <- protocolContexts instanceValue
  let (clientProcess, serverProcess) = processKeys network
      request = exactRequest instanceValue clientProcess serverProcess
  updated <- mapLeft show $ checkProcessCommunication
    instanceValue network contexts (JointProcessRendezvous request)
  clientContext <- requireProtocolContext clientProcess updated
  serverContext <- requireProtocolContext serverProcess updated
  assert (lookupProtocolEndpoint clientEndpoint clientContext == Nothing)
    "client predecessor endpoint survived joint rendezvous"
  assert (lookupProtocolEndpoint serverEndpoint serverContext == Nothing)
    "server predecessor endpoint survived joint rendezvous"
  clientSuccessorBinding <- maybe
    (Left "client successor endpoint missing") Right
    (lookupProtocolEndpoint clientSuccessor clientContext)
  serverSuccessorBinding <- maybe
    (Left "server successor endpoint missing") Right
    (lookupProtocolEndpoint serverSuccessor serverContext)
  let exactInstance = binaryProtocolInstanceRevision instanceValue
  assert
    ( protocolEndpointInstance clientSuccessorBinding == exactInstance
      && protocolEndpointInstance serverSuccessorBinding == exactInstance )
    "joint rendezvous changed protocol-instance identity"
  assert
    ( protocolEndpointRole clientSuccessorBinding == clientRole
      && protocolEndpointRole serverSuccessorBinding == serverRole )
    "joint rendezvous changed role identity"
  assert
    ( protocolEndpointSession clientSuccessorBinding == End doneOutcome
      && protocolEndpointSession serverSuccessorBinding == End doneOutcome )
    "joint rendezvous did not produce exact declared successor sessions"

unilateralProgressRejects :: Either String ()
unilateralProgressRejects = do
  instanceValue <- protocolInstance
  network <- activeNetwork
  contexts <- protocolContexts instanceValue
  let (clientProcess, _) = processKeys network
      exactInstance = binaryProtocolInstanceRevision instanceValue
      action = ProtocolSendRequest
        clientEndpoint clientSuccessor exactInstance clientRole
  case checkProcessCommunication instanceValue network contexts
      (UnilateralProcessAction clientProcess action) of
    Left (UnilateralRendezvousRejected process request) ->
      assert (process == clientProcess && request == action)
        "unilateral rejection lost exact process/action identity"
    other -> Left ("unilateral process action did not reject: " <> show other)

wrongInstanceRejects :: Either String ()
wrongInstanceRejects = do
  instanceValue <- protocolInstance
  network <- activeNetwork
  let (clientProcess, serverProcess) = processKeys network
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  wrongClient <- mapLeft show $ insertProtocolEndpoint
    clientEndpoint wrongInstance clientRole
    (protocolProjectionSession clientProjection)
    emptyProtocolContext
  server <- mapLeft show $ insertProtocolEndpoint
    serverEndpoint (binaryProtocolInstanceRevision instanceValue) serverRole
    (protocolProjectionSession serverProjection)
    emptyProtocolContext
  let contexts = Map.fromList
        [ (clientProcess, wrongClient)
        , (serverProcess, server)
        ]
      request = exactRequest instanceValue clientProcess serverProcess
  case checkProcessCommunication instanceValue network contexts
      (JointProcessRendezvous request) of
    Left (RendezvousProtocolInstanceMismatch process expected actual) ->
      assert
        ( process == clientProcess
          && expected == binaryProtocolInstanceRevision instanceValue
          && actual == wrongInstance )
        "wrong-instance rejection lost exact identities"
    other -> Left ("equal-shape wrong protocol instance was accepted: " <> show other)

wrongRoleRejects :: Either String ()
wrongRoleRejects = do
  instanceValue <- protocolInstance
  network <- activeNetwork
  let (clientProcess, serverProcess) = processKeys network
      exactInstance = binaryProtocolInstanceRevision instanceValue
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  wrongClient <- mapLeft show $ insertProtocolEndpoint
    clientEndpoint exactInstance serverRole
    (protocolProjectionSession clientProjection)
    emptyProtocolContext
  server <- mapLeft show $ insertProtocolEndpoint
    serverEndpoint exactInstance serverRole
    (protocolProjectionSession serverProjection)
    emptyProtocolContext
  let contexts = Map.fromList
        [ (clientProcess, wrongClient)
        , (serverProcess, server)
        ]
      request = exactRequest instanceValue clientProcess serverProcess
  case checkProcessCommunication instanceValue network contexts
      (JointProcessRendezvous request) of
    Left (RendezvousProtocolRoleMismatch process expected actual) ->
      assert
        (process == clientProcess && expected == clientRole && actual == serverRole)
        "wrong-role rejection lost exact role identities"
    other -> Left ("wrong exact role was accepted: " <> show other)

wrongProcessBindingRejects :: Either String ()
wrongProcessBindingRejects = do
  instanceValue <- protocolInstance
  network <- activeNetwork
  normal <- protocolContexts instanceValue
  let (clientProcess, serverProcess) = processKeys network
  clientContext <- requireProtocolContext clientProcess normal
  serverContext <- requireProtocolContext serverProcess normal
  let swapped = Map.fromList
        [ (clientProcess, serverContext)
        , (serverProcess, clientContext)
        ]
      request = exactRequest instanceValue clientProcess serverProcess
  case checkProcessCommunication instanceValue network swapped
      (JointProcessRendezvous request) of
    Left (RendezvousEndpointNotOwnedByProcess process endpoint) ->
      assert (process == clientProcess && endpoint == clientEndpoint)
        "wrong-process rejection lost process/endpoint identity"
    other -> Left ("wrong process binding was accepted: " <> show other)

protocolInstance :: Either String BinaryProtocolInstance
protocolInstance = mapLeft show $ instantiateBinaryProtocol
  strictGenericInstantiationPolicy
  rendezvousFamily
  []
  []

rendezvousFamily :: BinaryProtocolFamily
rendezvousFamily = BinaryProtocolFamily
  { protocolFamilyDeclarationKey = DeclarationKey "protocol.conc004"
  , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.conc004.v1"
  , protocolFamilyRequirements = Set.empty
  , protocolFamilyPrimaryRole = clientRole
  , protocolFamilyPeerRole = serverRole
  , protocolFamilyPrimarySession = ProtocolTemplateSend
      (Name "message")
      (ProtocolConcreteType TyUnit)
      (ProtocolTemplateEnd doneOutcome)
  }

protocolContexts
  :: BinaryProtocolInstance
  -> Either String (Map.Map ProcessKey ProtocolContext)
protocolContexts instanceValue = do
  network <- activeNetwork
  let (clientProcess, serverProcess) = processKeys network
      exactInstance = binaryProtocolInstanceRevision instanceValue
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  clientContext <- mapLeft show $ insertProtocolEndpoint
    clientEndpoint exactInstance clientRole
    (protocolProjectionSession clientProjection)
    emptyProtocolContext
  serverContext <- mapLeft show $ insertProtocolEndpoint
    serverEndpoint exactInstance serverRole
    (protocolProjectionSession serverProjection)
    emptyProtocolContext
  pure $ Map.fromList
    [ (clientProcess, clientContext)
    , (serverProcess, serverContext)
    ]

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

activeNetwork :: Either String ProcessNetwork
activeNetwork = do
  graph <- mapLeft show rootGraph
  network <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  mapLeft show $ activateRootProcesses network

processKeys :: ProcessNetwork -> (ProcessKey, ProcessKey)
processKeys network =
  let rootRevision = identityInstanceRevision (processNetworkRoot network)
  in ( deriveProcessKey rootRevision (processSiteKey siteA)
     , deriveProcessKey rootRevision (processSiteKey siteB)
     )

requireProtocolContext
  :: ProcessKey
  -> Map.Map ProcessKey ProtocolContext
  -> Either String ProtocolContext
requireProtocolContext processKey contexts =
  maybe (Left "missing process protocol context") Right (Map.lookup processKey contexts)

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

doneOutcome :: Outcome
doneOutcome = Outcome "done"

wrongInstance :: ProtocolInstanceRevision
wrongInstance = ProtocolInstanceRevision "protocol.conc004.wrong"

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
