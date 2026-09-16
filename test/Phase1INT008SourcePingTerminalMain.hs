{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessEndpointClosure
import Phil.Core.ProcessLifecycle
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( grammarV1CheckedArchitectureSurface
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.ComponentReceiveClose
import Phil.Surface.GrammarV1.ComponentReceiveProvisioning
import Phil.Surface.GrammarV1.ComponentSendClose
import Phil.Surface.GrammarV1.ComponentSendProvisioning
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolEndpointType
  ( GrammarV1ProtocolEndpointResolution (..)
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedBinaryProtocolFamily
  )
import Phil.Surface.GrammarV1.SemanticComponentHeader
  ( grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-008 ordinary source Ping reaches root terminal"
        sourcePingReachesRootTerminal
    , test "INT-008 receive source type must match projected protocol message"
        receiveTypeMismatchRejects
    , test "INT-008 source-derived rendezvous names are semantic binder names"
        sourceRendezvousUsesExactBinderNames
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

data SourcePingFixture = SourcePingFixture
  { fixtureInstance :: BinaryProtocolInstance
  , fixtureNetwork :: ProcessNetwork
  , fixtureCommunication :: ProcessCommunicationState
  , fixtureClientSend :: GrammarV1ResolvedComponentSend
  , fixtureServerReceive :: GrammarV1ResolvedComponentReceive
  , fixtureClientProcess :: ProcessKey
  , fixtureServerProcess :: ProcessKey
  }

sourcePingReachesRootTerminal :: Either String ()
sourcePingReachesRootTerminal = do
  fx <- sourcePingFixture source
  let clientSide = resolvedComponentSendRendezvousSide (fixtureClientSend fx)
      serverSide = resolvedComponentReceiveRendezvousSide (fixtureServerReceive fx)
      exactInstance = binaryProtocolInstanceRevision (fixtureInstance fx)
  closedClient <- mapLeft show $ closeProcessEndpointState
    (fixtureNetwork fx)
    (fixtureCommunication fx)
    (fixtureClientProcess fx)
    (rendezvousSuccessor clientSide)
    exactInstance
    (rendezvousRole clientSide)
    doneOutcome
  closedBoth <- mapLeft show $ closeProcessEndpointState
    (fixtureNetwork fx)
    closedClient
    (fixtureServerProcess fx)
    (rendezvousSuccessor serverSide)
    exactInstance
    (rendezvousRole serverSide)
    doneOutcome
  assert (Map.null (communicationRestrictedOwners closedBoth))
    "source-derived closed Ping left restricted endpoint owners"
  assert
    (all (Map.null . protocolEndpoints)
      (Map.elems (communicationProtocolContexts closedBoth)))
    "source-derived closed Ping left protocol endpoint metadata"
  runtime0 <- mapLeft show $ initializeProcessRuntime
    (fixtureNetwork fx)
    (communicationProtocolContexts closedBoth)
  runtime1 <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition (fixtureClientProcess fx)) runtime0
  runtime2 <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition (fixtureServerProcess fx)) runtime1
  disposition <- mapLeft show $ classifyProcessNetwork emptyRootClosure [] runtime2
  case disposition of
    NetworkTerminal fact ->
      assert
        (Map.keysSet (rootTerminalProcesses fact)
          == Map.keysSet (processNetworkPopulation (fixtureNetwork fx)))
        "root terminal fact did not cover source-derived Ping process population"
    other -> Left ("source-derived Ping network was not root terminal: " <> show other)

receiveTypeMismatchRejects :: Either String ()
receiveTypeMismatchRejects = do
  (protocol, _client, server, architectureDecl) <- parseSource wrongReceiveTypeSource
  family <- protocolFamily protocol
  instanceValue <- instantiate family
  let resolution = endpointResolution instanceValue
      occurrence = protocolOccurrence instanceValue
  header <- semanticHeader serverKey serverRevision resolution server
  architecture <- checkedArchitecture architectureDecl
  graph <- mapLeft show rootGraph
  network <- mapLeft show $ elaborateProcessNetwork graph [clientSite, serverSite]
  let (_, serverProcess) = processKeys network
  provisioning <- mapLeft show $ grammarV1ResolveArchitectureComponentProvisioning
    architecture "server" "server_run" serverProcess server header [occurrence]
  plan <- case grammarV1CheckedComponentReceiveClose serverKey server of
    Just (Right value) -> Right value
    other -> Left ("expected server receive plan, got " <> show other)
  case grammarV1ResolveComponentReceiveProvisioning
      emptyStaticContext plan provisioning of
    Left (GrammarV1ComponentReceiveMessageTypeMismatch (TyUInt 8) (TyUInt 16)) -> Right ()
    other -> Left ("wrong written receive type did not reject exactly: " <> show other)

sourceRendezvousUsesExactBinderNames :: Either String ()
sourceRendezvousUsesExactBinderNames = do
  fx <- sourcePingFixture source
  let clientResolved = fixtureClientSend fx
      serverResolved = fixtureServerReceive fx
      clientSide = resolvedComponentSendRendezvousSide clientResolved
      serverSide = resolvedComponentReceiveRendezvousSide serverResolved
      clientEndpointBinder = provisionedComponentParameterBinder
        (resolvedComponentSendEndpointParameter clientResolved)
      serverEndpointBinder = provisionedComponentParameterBinder
        (resolvedComponentReceiveEndpointParameter serverResolved)
      serverPayloadBinder = resolvedComponentReceivePayloadBinder serverResolved
  assert
    (rendezvousEndpoint clientSide == grammarV1ResolvedBinderCoreName clientEndpointBinder)
    "client rendezvous predecessor was not exact provisioned source binder name"
  assert
    (rendezvousEndpoint serverSide == grammarV1ResolvedBinderCoreName serverEndpointBinder)
    "server rendezvous predecessor was not exact provisioned source binder name"
  assert
    (grammarV1ResolvedBinderKind serverPayloadBinder == GrammarV1LetPatternBinder)
    "received U8 value did not retain source let-pattern binder identity"
  assert
    (resolvedComponentSendPayloadOccurrence clientResolved
      == ActivationOccurrenceKey
        "phil.architecture.entry.v1:architecture.local-ping.v1:payload")
    "client send lost exact architecture entry provenance"

sourcePingFixture :: Text -> Either String SourcePingFixture
sourcePingFixture sourceText = do
  (protocol, client, server, architectureDecl) <- parseSource sourceText
  family <- protocolFamily protocol
  instanceValue <- instantiate family
  let resolution = endpointResolution instanceValue
      occurrence = protocolOccurrence instanceValue
  clientHeader <- semanticHeader clientKey clientRevision resolution client
  serverHeader <- semanticHeader serverKey serverRevision resolution server
  architecture <- checkedArchitecture architectureDecl
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [clientSite, serverSite]
  let (clientProcess, serverProcess) = processKeys network0
  clientProvisioning <- mapLeft show $ grammarV1ResolveArchitectureComponentProvisioning
    architecture "client" "client_run" clientProcess client clientHeader [occurrence]
  serverProvisioning <- mapLeft show $ grammarV1ResolveArchitectureComponentProvisioning
    architecture "server" "server_run" serverProcess server serverHeader [occurrence]
  clientPlan <- case grammarV1CheckedComponentSendClose clientKey client of
    Just (Right value) -> Right value
    other -> Left ("expected checked ClientWorker send plan, got " <> show other)
  serverPlan <- case grammarV1CheckedComponentReceiveClose serverKey server of
    Just (Right value) -> Right value
    other -> Left ("expected checked ServerWorker receive plan, got " <> show other)
  clientSend <- mapLeft show $ grammarV1ResolveComponentSendProvisioning
    clientPlan clientProvisioning
  serverReceive <- mapLeft show $ grammarV1ResolveComponentReceiveProvisioning
    emptyStaticContext serverPlan serverProvisioning
  clientActivation <- mapLeft show $ grammarV1ResolvedComponentActivation clientProvisioning
  serverActivation <- mapLeft show $ grammarV1ResolvedComponentActivation serverProvisioning
  (network, activationState) <- mapLeft show $ activateProcessState
    network0
    [ resolvedComponentActivationContract clientActivation
    , resolvedComponentActivationContract serverActivation
    ]
  clientContext <- mapLeft show $
    grammarV1ComponentProtocolContextFromActivation clientActivation activationState
  serverContext <- mapLeft show $
    grammarV1ComponentProtocolContextFromActivation serverActivation activationState
  communication0 <- mapLeft show $ communicationStateFromActivation
    activationState
    (Map.fromList
      [ (clientProcess, clientContext)
      , (serverProcess, serverContext)
      ])
  let request = SendReceiveRendezvous
        (resolvedComponentSendRendezvousSide clientSend)
        (resolvedComponentReceiveRendezvousSide serverReceive)
  communication <- mapLeft show $
    checkProcessCommunicationState instanceValue network communication0 request
  Right SourcePingFixture
    { fixtureInstance = instanceValue
    , fixtureNetwork = network
    , fixtureCommunication = communication
    , fixtureClientSend = clientSend
    , fixtureServerReceive = serverReceive
    , fixtureClientProcess = clientProcess
    , fixtureServerProcess = serverProcess
    }

protocolFamily :: GrammarV1ProtocolDecl -> Either String BinaryProtocolFamily
protocolFamily protocol =
  case grammarV1ClosedBinaryProtocolFamily
      protocolKey protocolInterface protocol of
    Just (Right value) -> Right value
    other -> Left ("expected closed Ping protocol family, got " <> show other)

instantiate :: BinaryProtocolFamily -> Either String BinaryProtocolInstance
instantiate family = mapLeft show $
  instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []

endpointResolution :: BinaryProtocolInstance -> GrammarV1ProtocolEndpointResolution
endpointResolution instanceValue = GrammarV1ProtocolEndpointResolution
  { protocolEndpointResolutionSourceReference = ReferencedGenericStaticActual "Ping"
  , protocolEndpointResolutionInstance = instanceValue
  }

protocolOccurrence :: BinaryProtocolInstance -> GrammarV1ArchitectureProtocolOccurrence
protocolOccurrence instanceValue = GrammarV1ArchitectureProtocolOccurrence
  { architectureProtocolOccurrenceName = "ping"
  , architectureProtocolOccurrenceSourceReference = ReferencedGenericStaticActual "Ping"
  , architectureProtocolOccurrenceInstance = instanceValue
  }

semanticHeader
  :: DeclarationKey
  -> DefinitionRevision
  -> GrammarV1ProtocolEndpointResolution
  -> GrammarV1ComponentDecl
  -> Either String GrammarV1CheckedSemanticComponentHeader
semanticHeader declarationKey revision resolution component =
  case grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
      emptyStaticContext [resolution] declarationKey revision component of
    Just (Right (value, [])) -> Right value
    other -> Left ("expected endpoint-aware component header, got " <> show other)

checkedArchitecture
  :: GrammarV1ArchitectureDecl
  -> Either String GrammarV1CheckedArchitectureSurface
checkedArchitecture architectureDecl =
  case grammarV1CheckedArchitectureSurface
      emptyStaticContext architectureKey architectureRevision architectureDecl of
    Just (Right value) -> Right value
    other -> Left ("expected checked LocalPing architecture, got " <> show other)

parseSource
  :: Text
  -> Either String
      ( GrammarV1ProtocolDecl
      , GrammarV1ComponentDecl
      , GrammarV1ComponentDecl
      , GrammarV1ArchitectureDecl
      )
parseSource sourceText = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int008-source-ping-terminal" sourceText
  case grammarV1TopLevelDecls sourceFile of
    [ Located _ protocolTop
      , Located _ clientTop
      , Located _ serverTop
      , Located _ architectureTop
      , Located _ programTop
      ] -> do
        protocol <- declarationAsProtocol protocolTop
        client <- declarationAsComponent "ClientWorker" clientTop
        server <- declarationAsComponent "ServerWorker" serverTop
        architecture <- declarationAsArchitecture architectureTop
        case locatedValue (grammarV1Declaration programTop) of
          GrammarV1ProgramDeclaration _ -> Right ()
          other -> Left ("expected program declaration, got " <> show other)
        Right (protocol, client, server, architecture)
    declarations -> Left
      ("expected protocol/two components/architecture/program, got "
        <> show (length declarations) <> " declarations")

source, wrongReceiveTypeSource :: Text
source = sourceWithReceiveType "U8"
wrongReceiveTypeSource = sourceWithReceiveType "U16"

sourceWithReceiveType :: Text -> Text
sourceWithReceiveType receiveType = Text.unlines
  [ "protocol Ping {"
  , "  role Client = send (x : U8) then end Done;"
  , "  role Server = receive (x : U8) then end Done;"
  , "}"
  , "component ClientWorker(endpoint : Client[Ping], payload : U8) {"
  , "  let done = send payload on endpoint;"
  , "  close done;"
  , "}"
  , "component ServerWorker(endpoint : Server[Ping]) {"
  , "  let (done, received) = receive " <> receiveType <> " on endpoint;"
  , "  close done;"
  , "}"
  , "architecture LocalPing {"
  , "  instance client = ClientWorker;"
  , "  instance server = ServerWorker;"
  , "  process client_run = client;"
  , "  process server_run = server;"
  , "  protocol ping = Ping;"
  , "  role ping.Client = client;"
  , "  role ping.Server = server;"
  , "  entry payload : U8;"
  , "  bind client.endpoint = ping.Client;"
  , "  bind client.payload = payload;"
  , "  bind server.endpoint = ping.Server;"
  , "}"
  , "program main = instantiate LocalPing;"
  ]

declarationAsProtocol :: GrammarV1TopLevelDecl -> Either String GrammarV1ProtocolDecl
declarationAsProtocol top = case locatedValue (grammarV1Declaration top) of
  GrammarV1ProtocolDeclaration value -> Right value
  other -> Left ("expected protocol declaration, got " <> show other)

declarationAsComponent
  :: Text
  -> GrammarV1TopLevelDecl
  -> Either String GrammarV1ComponentDecl
declarationAsComponent expected top = case locatedValue (grammarV1Declaration top) of
  GrammarV1ComponentDeclaration value
    | locatedValue (grammarV1ComponentName value) == expected -> Right value
    | otherwise -> Left ("unexpected component declaration " <> show value)
  other -> Left ("expected component declaration, got " <> show other)

declarationAsArchitecture
  :: GrammarV1TopLevelDecl
  -> Either String GrammarV1ArchitectureDecl
declarationAsArchitecture top = case locatedValue (grammarV1Declaration top) of
  GrammarV1ArchitectureDeclaration value -> Right value
  other -> Left ("expected architecture declaration, got " <> show other)

terminalTransition :: ProcessKey -> DeclaredTerminalTransition
terminalTransition processKey = DeclaredTerminalTransition
  { declaredTerminalProcess = processKey
  , declaredTerminalControl = Closed doneOutcome
  , declaredTerminalDisposals = []
  }

emptyRootClosure :: RootClosureState
emptyRootClosure = RootClosureState Set.empty Set.empty Set.empty

processKeys :: ProcessNetwork -> (ProcessKey, ProcessKey)
processKeys network =
  let rootRevision = identityInstanceRevision (processNetworkRoot network)
  in ( deriveProcessKey rootRevision (processSiteKey clientSite)
     , deriveProcessKey rootRevision (processSiteKey serverSite)
     )

rootGraph :: Either ArchitectureInstantiationError ArchitectureInstanceGraph
rootGraph = instantiateArchitecture rootKey rootSpec

rootSpec :: ArchitectureNodeSpec
rootSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "root"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren =
      [ ArchitectureChildSpec clientSlot clientWorkerSpec
      , ArchitectureChildSpec serverSlot serverWorkerSpec
      ]
  , architectureNodeReferences = []
  }

clientWorkerSpec, serverWorkerSpec :: ArchitectureNodeSpec
clientWorkerSpec = leafSpec "ClientWorker"
serverWorkerSpec = leafSpec "ServerWorker"

leafSpec :: Text -> ArchitectureNodeSpec
leafSpec label = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration label
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

declaration :: Text -> DeclarationIdentity
declaration label = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation label []
  , declarationKey = DeclarationKey ("decl-" <> label)
  , declarationInterfaceSemantics = SemanticAtom "interface"
  , declarationDefinitionSemantics = SemanticAtom "definition"
  }

clientSite, serverSite :: ProcessDeclarationSite
clientSite = ProcessDeclarationSite (ProcessSiteKey "client_run") clientTarget
serverSite = ProcessDeclarationSite (ProcessSiteKey "server_run") serverTarget

rootKey, clientTarget, serverTarget :: InstanceKey
rootKey = InstanceKey "root-instance"
clientTarget = scopedInstanceKey rootKey clientSlot
serverTarget = scopedInstanceKey rootKey serverSlot

clientSlot, serverSlot :: OccurrenceSlotKey
clientSlot = OccurrenceSlotKey "client"
serverSlot = OccurrenceSlotKey "server"

protocolKey, clientKey, serverKey, architectureKey :: DeclarationKey
protocolKey = DeclarationKey "protocol.ping"
clientKey = DeclarationKey "component.ClientWorker"
serverKey = DeclarationKey "component.ServerWorker"
architectureKey = DeclarationKey "architecture.LocalPing"

protocolInterface :: InterfaceRevision
protocolInterface = InterfaceRevision "protocol.ping.v1"

clientRevision, serverRevision, architectureRevision :: DefinitionRevision
clientRevision = DefinitionRevision "component.ClientWorker.v1"
serverRevision = DefinitionRevision "component.ServerWorker.v1"
architectureRevision = DefinitionRevision "architecture.local-ping.v1"

doneOutcome :: Outcome
doneOutcome = Outcome "Done"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
