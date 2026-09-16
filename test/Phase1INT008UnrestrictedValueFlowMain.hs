{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol (ProtocolContext (..))
import Phil.Core.Protocol.Family
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  )
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureSurface
  , grammarV1CheckedArchitectureSurface
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.ComponentReceiveClose
import Phil.Surface.GrammarV1.ComponentReceiveProvisioning
import Phil.Surface.GrammarV1.ComponentSendClose
import Phil.Surface.GrammarV1.ComponentSendProvisioning
import Phil.Surface.GrammarV1.ComponentUnrestrictedRendezvous
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolEndpointType
  ( GrammarV1ProtocolEndpointResolution (..)
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedBinaryProtocolFamily
  )
import Phil.Surface.GrammarV1.SemanticComponentHeader
  ( GrammarV1CheckedSemanticComponentHeader
  , grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-008 whole-source Ping carries exact unrestricted U8 value"
        exactUnrestrictedValueFlows
    , test "INT-008 unrestricted value rejects wrong root-entry occurrence"
        wrongEntryOccurrenceRejects
    , test "INT-008 unrestricted value rejects wrong scalar width"
        wrongScalarTypeRejects
    , test "INT-008 unrestricted value rejects out-of-range scalar"
        outOfRangeScalarRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

data Fixture = Fixture
  { fixtureInstance :: BinaryProtocolInstance
  , fixtureNetwork :: ProcessNetwork
  , fixtureCommunication :: ProcessCommunicationState
  , fixtureSend :: GrammarV1ResolvedComponentSend
  , fixtureReceive :: GrammarV1ResolvedComponentReceive
  , fixtureClientProcess :: ProcessKey
  , fixtureServerProcess :: ProcessKey
  }

exactUnrestrictedValueFlows :: Either String ()
exactUnrestrictedValueFlows = do
  fx <- sourceFixture
  let send = fixtureSend fx
      receive = fixtureReceive fx
      value = ScalarUIntLiteral 8 42
      rootValue = GrammarV1RootEntryScalar
        (resolvedComponentSendPayloadOccurrence send)
        value
  (communication, flow) <- mapLeft show $
    grammarV1CheckUnrestrictedComponentRendezvous
      (fixtureInstance fx)
      (fixtureNetwork fx)
      (fixtureCommunication fx)
      send
      receive
      rootValue
  assert
    (unrestrictedValueFlowEntryOccurrence flow
      == resolvedComponentSendPayloadOccurrence send)
    "value flow changed exact architecture entry occurrence"
  assert
    (unrestrictedValueFlowSenderBinder flow
      == provisionedComponentParameterBinder
        (resolvedComponentSendPayloadParameter send))
    "value flow changed exact source sender binder"
  assert
    (unrestrictedValueFlowReceiverBinder flow
      == resolvedComponentReceivePayloadBinder receive)
    "value flow changed exact source receive binder"
  assert
    (unrestrictedValueFlowType flow == TyUInt 8)
    "value flow changed Ping payload type"
  assert
    (unrestrictedValueFlowValue flow == value)
    "received value evidence differs from root-entry scalar"
  let clientSide = resolvedComponentSendRendezvousSide send
      serverSide = resolvedComponentReceiveRendezvousSide receive
  clientContext <- requireContext communication (fixtureClientProcess fx)
  serverContext <- requireContext communication (fixtureServerProcess fx)
  assert
    (Map.member (rendezvousSuccessor clientSide) (protocolEndpoints clientContext))
    "value-bearing rendezvous did not advance client endpoint"
  assert
    (Map.member (rendezvousSuccessor serverSide) (protocolEndpoints serverContext))
    "value-bearing rendezvous did not advance server endpoint"

wrongEntryOccurrenceRejects :: Either String ()
wrongEntryOccurrenceRejects = do
  fx <- sourceFixture
  let send = fixtureSend fx
      expected = resolvedComponentSendPayloadOccurrence send
      actual = ActivationOccurrenceKey "wrong-entry"
  case grammarV1CheckUnrestrictedComponentRendezvous
      (fixtureInstance fx)
      (fixtureNetwork fx)
      (fixtureCommunication fx)
      send
      (fixtureReceive fx)
      (GrammarV1RootEntryScalar actual (ScalarUIntLiteral 8 42)) of
    Left (GrammarV1UnrestrictedRendezvousEntryOccurrenceMismatch
      expected' actual') ->
        assert (expected' == expected && actual' == actual)
          "entry-occurrence diagnostic changed exact identities"
    other -> Left ("wrong root-entry occurrence did not reject exactly: " <> show other)

wrongScalarTypeRejects :: Either String ()
wrongScalarTypeRejects = do
  fx <- sourceFixture
  let send = fixtureSend fx
      rootValue = GrammarV1RootEntryScalar
        (resolvedComponentSendPayloadOccurrence send)
        (ScalarUIntLiteral 16 42)
  case grammarV1CheckUnrestrictedComponentRendezvous
      (fixtureInstance fx)
      (fixtureNetwork fx)
      (fixtureCommunication fx)
      send
      (fixtureReceive fx)
      rootValue of
    Left (GrammarV1UnrestrictedRendezvousScalarTypeMismatch
      (TyUInt 8) (TyUInt 16)) -> Right ()
    other -> Left ("wrong scalar width did not reject exactly: " <> show other)

outOfRangeScalarRejects :: Either String ()
outOfRangeScalarRejects = do
  fx <- sourceFixture
  let send = fixtureSend fx
      literal = ScalarUIntLiteral 8 256
      rootValue = GrammarV1RootEntryScalar
        (resolvedComponentSendPayloadOccurrence send)
        literal
  case grammarV1CheckUnrestrictedComponentRendezvous
      (fixtureInstance fx)
      (fixtureNetwork fx)
      (fixtureCommunication fx)
      send
      (fixtureReceive fx)
      rootValue of
    Left (GrammarV1UnrestrictedRendezvousScalarOutOfRange actual) ->
      assert (actual == literal) "range diagnostic changed scalar literal"
    other -> Left ("out-of-range U8 did not reject exactly: " <> show other)

sourceFixture :: Either String Fixture
sourceFixture = do
  (protocol, client, server, architectureDecl) <- parseSource
  family <- protocolFamily protocol
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  let resolution = GrammarV1ProtocolEndpointResolution
        { protocolEndpointResolutionSourceReference =
            ReferencedGenericStaticActual "Ping"
        , protocolEndpointResolutionInstance = instanceValue
        }
      occurrence = GrammarV1ArchitectureProtocolOccurrence
        { architectureProtocolOccurrenceName = "ping"
        , architectureProtocolOccurrenceSourceReference =
            ReferencedGenericStaticActual "Ping"
        , architectureProtocolOccurrenceInstance = instanceValue
        }
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
  send <- mapLeft show $ grammarV1ResolveComponentSendProvisioning
    clientPlan clientProvisioning
  receive <- mapLeft show $ grammarV1ResolveComponentReceiveProvisioning
    emptyStaticContext serverPlan serverProvisioning
  clientActivation <- mapLeft show $
    grammarV1ResolvedComponentActivation clientProvisioning
  serverActivation <- mapLeft show $
    grammarV1ResolvedComponentActivation serverProvisioning
  (network, activationState) <- mapLeft show $ activateProcessState
    network0
    [ resolvedComponentActivationContract clientActivation
    , resolvedComponentActivationContract serverActivation
    ]
  clientContext <- mapLeft show $
    grammarV1ComponentProtocolContextFromActivation clientActivation activationState
  serverContext <- mapLeft show $
    grammarV1ComponentProtocolContextFromActivation serverActivation activationState
  communication <- mapLeft show $ communicationStateFromActivation
    activationState
    (Map.fromList
      [ (clientProcess, clientContext)
      , (serverProcess, serverContext)
      ])
  Right Fixture
    { fixtureInstance = instanceValue
    , fixtureNetwork = network
    , fixtureCommunication = communication
    , fixtureSend = send
    , fixtureReceive = receive
    , fixtureClientProcess = clientProcess
    , fixtureServerProcess = serverProcess
    }

requireContext
  :: ProcessCommunicationState
  -> ProcessKey
  -> Either String ProtocolContext
requireContext communication processKey =
  maybe
    (Left ("missing progressed protocol context for " <> show processKey))
    Right
    (Map.lookup processKey (communicationProtocolContexts communication))

protocolFamily :: GrammarV1ProtocolDecl -> Either String BinaryProtocolFamily
protocolFamily protocol =
  case grammarV1ClosedBinaryProtocolFamily
      protocolKey protocolInterface protocol of
    Just (Right value) -> Right value
    other -> Left ("expected closed Ping protocol family, got " <> show other)

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
  :: Either String
      ( GrammarV1ProtocolDecl
      , GrammarV1ComponentDecl
      , GrammarV1ComponentDecl
      , GrammarV1ArchitectureDecl
      )
parseSource = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int008-unrestricted-value-flow" source
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

source :: Text
source = Text.unlines
  [ "protocol Ping {"
  , "  role Client = send (x : U8) then end Done;"
  , "  role Server = receive (x : U8) then end Done;"
  , "}"
  , "component ClientWorker(endpoint : Client[Ping], payload : U8) {"
  , "  let done = send payload on endpoint;"
  , "  close done;"
  , "}"
  , "component ServerWorker(endpoint : Server[Ping]) {"
  , "  let (done, received) = receive U8 on endpoint;"
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

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
