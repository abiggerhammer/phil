{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Authority
  ( AuthorityExerciseSource (..)
  , AuthorityState
  , CapabilityOccurrenceKey (..)
  , emptyAuthorityState
  , insertAuthorityCapability
  )
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessEndpointClosure
import Phil.Core.ProcessLifecycle
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.IO.Console
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureSurface
  , grammarV1CheckedArchitectureSurface
  )
import Phil.Surface.GrammarV1.ComponentRequestReplyOutput
import Phil.Surface.GrammarV1.ComponentRequestReplyRuntime
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
    [ test "INT-009 whole-source request/reply writes exact reply and reaches terminal"
        wholeSourceRoundTripOutputsAndTerminates
    , test "INT-009 request value retains exact root-entry and receive-binder provenance"
        requestValueProvenanceIsExact
    , test "INT-009 reply value reaches exact receive binder and standard.stdout"
        replyOutputProvenanceIsExact
    , test "INT-009 wrong root-entry occurrence rejects before returning successor state"
        wrongEntryOccurrenceRejects
    , test "INT-009 console output requires possessed exact stdout authority"
        missingStdoutAuthorityRejects
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
  , fixtureResolved :: GrammarV1ResolvedRequestReply
  , fixtureClientProcess :: ProcessKey
  , fixtureServerProcess :: ProcessKey
  }

wholeSourceRoundTripOutputsAndTerminates :: Either String ()
wholeSourceRoundTripOutputsAndTerminates = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (communication, evidence) <- runSuccess fx authority
  let exactInstance = binaryProtocolInstanceRevision (fixtureInstance fx)
      replyRequest = resolvedRequestReplyReplyRequest (fixtureResolved fx)
  (serverRole, clientRole) <- case replyRequest of
    SendReceiveRendezvous serverSide clientSide ->
      Right (rendezvousRole serverSide, rendezvousRole clientSide)
    other -> Left ("expected reply send/receive request, got " <> show other)
  closedClient <- mapLeft show $ closeProcessEndpointState
    (fixtureNetwork fx)
    communication
    (fixtureClientProcess fx)
    (resolvedRequestReplyClientTerminalEndpoint (fixtureResolved fx))
    exactInstance
    clientRole
    doneOutcome
  closedBoth <- mapLeft show $ closeProcessEndpointState
    (fixtureNetwork fx)
    closedClient
    (fixtureServerProcess fx)
    (resolvedRequestReplyServerTerminalEndpoint (fixtureResolved fx))
    exactInstance
    serverRole
    doneOutcome
  assert (Map.null (communicationRestrictedOwners closedBoth))
    "request/reply terminal close left restricted owners"
  assert
    (all (Map.null . protocolEndpoints)
      (Map.elems (communicationProtocolContexts closedBoth)))
    "request/reply terminal close left endpoint metadata"
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
        "root terminal fact did not cover request/reply process population"
    other -> Left ("request/reply network was not root terminal: " <> show other)
  assert
    (checkedConsoleWriteOutcome (requestReplyEvidenceConsoleWrite evidence)
      == ConsoleWriteSucceeded)
    "successful witness did not retain successful console outcome"

requestValueProvenanceIsExact :: Either String ()
requestValueProvenanceIsExact = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (_, evidence) <- runSuccess fx authority
  let resolved = fixtureResolved fx
      payloadParameter = resolvedRequestReplyClientPayloadParameter resolved
  assert
    (requestReplyEvidenceRequestOccurrence evidence
      == resolvedRequestReplyRequestOccurrence resolved)
    "request value changed exact root-entry occurrence"
  assert
    (requestReplyEvidenceRequestSenderBinder evidence
      == provisionedComponentParameterBinder payloadParameter)
    "request value changed exact sender parameter binder"
  assert
    (requestReplyEvidenceRequestReceiverBinder evidence
      == resolvedRequestReplyRequestReceiverBinder resolved)
    "request value changed exact server receive binder"
  assert
    (requestReplyEvidenceRequestValue evidence == ScalarUIntLiteral 8 42)
    "request value changed concrete U8 payload"

replyOutputProvenanceIsExact :: Either String ()
replyOutputProvenanceIsExact = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (_, evidence) <- runSuccess fx authority
  let resolved = fixtureResolved fx
      checkedWrite = requestReplyEvidenceConsoleWrite evidence
      stdout = consoleEnvironmentStdout standardConsoleEnvironment
      expectedEffect = consoleOperationEffect stdout ConsoleWriteOp
  assert (requestReplyEvidenceReplySenderText evidence == "pong")
    "server reply text changed"
  assert
    (requestReplyEvidenceReplyReceiverBinder evidence
      == resolvedRequestReplyReplyReceiverBinder resolved)
    "reply value changed exact client receive binder"
  assert (checkedConsoleWriteRequestedText checkedWrite == "pong")
    "console write did not observe the exact received reply"
  assert (checkedConsoleWriteOccurrence checkedWrite == stdout)
    "reply output did not target exact standard.stdout occurrence"
  assert (checkedConsoleWriteEffect checkedWrite == expectedEffect)
    "reply output lost exact subject-indexed console effect"
  assert (checkedConsoleWriteObservablePrefix checkedWrite == "pong")
    "successful console write changed observable reply text"

wrongEntryOccurrenceRejects :: Either String ()
wrongEntryOccurrenceRejects = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  case grammarV1RunRequestReply
      (fixtureInstance fx)
      (fixtureNetwork fx)
      (fixtureCommunication fx)
      (fixtureResolved fx)
      (ActivationOccurrenceKey "wrong-entry")
      (ScalarUIntLiteral 8 42)
      (PossessedCapability stdoutCapability)
      authority
      ConsoleWriteSucceeded of
    Left (GrammarV1RequestReplyEntryOccurrenceMismatch expected actual) -> do
      assert (expected == resolvedRequestReplyRequestOccurrence (fixtureResolved fx))
        "entry mismatch changed expected occurrence"
      assert (actual == ActivationOccurrenceKey "wrong-entry")
        "entry mismatch changed actual occurrence"
    other -> Left ("wrong entry occurrence did not reject exactly: " <> show other)

missingStdoutAuthorityRejects :: Either String ()
missingStdoutAuthorityRejects = do
  fx <- sourceFixture
  case grammarV1RunRequestReply
      (fixtureInstance fx)
      (fixtureNetwork fx)
      (fixtureCommunication fx)
      (fixtureResolved fx)
      (resolvedRequestReplyRequestOccurrence (fixtureResolved fx))
      (ScalarUIntLiteral 8 42)
      (PossessedCapability stdoutCapability)
      emptyAuthorityState
      ConsoleWriteSucceeded of
    Left (GrammarV1RequestReplyConsoleError _) -> Right ()
    other -> Left ("missing stdout authority did not reject output: " <> show other)

runSuccess
  :: Fixture
  -> AuthorityState
  -> Either String (ProcessCommunicationState, GrammarV1RequestReplyRuntimeEvidence)
runSuccess fx authority = mapLeft show $ grammarV1RunRequestReply
  (fixtureInstance fx)
  (fixtureNetwork fx)
  (fixtureCommunication fx)
  (fixtureResolved fx)
  (resolvedRequestReplyRequestOccurrence (fixtureResolved fx))
  (ScalarUIntLiteral 8 42)
  (PossessedCapability stdoutCapability)
  authority
  ConsoleWriteSucceeded

stdoutAuthority :: Either String AuthorityState
stdoutAuthority = do
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  capability <- mapLeft show $
    defaultConsoleAuthorityCapability stdoutCapability stdout
  mapLeft show (insertAuthorityCapability capability emptyAuthorityState)

sourceFixture :: Either String Fixture
sourceFixture = do
  (protocol, client, server, architectureDecl) <- parseSource
  family <- protocolFamily protocol
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  let resolution = GrammarV1ProtocolEndpointResolution
        { protocolEndpointResolutionSourceReference =
            ReferencedGenericStaticActual "PingRoundTrip"
        , protocolEndpointResolutionInstance = instanceValue
        }
      occurrence = GrammarV1ArchitectureProtocolOccurrence
        { architectureProtocolOccurrenceName = "ping"
        , architectureProtocolOccurrenceSourceReference =
            ReferencedGenericStaticActual "PingRoundTrip"
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
  clientPlan <- case grammarV1CheckedRequestReplyClient clientKey client of
    Just (Right value) -> Right value
    other -> Left ("expected checked request/reply client, got " <> show other)
  serverPlan <- case grammarV1CheckedRequestReplyServer serverKey server of
    Just (Right value) -> Right value
    other -> Left ("expected checked request/reply server, got " <> show other)
  resolved <- mapLeft show $ grammarV1ResolveRequestReply
    clientPlan clientProvisioning serverPlan serverProvisioning
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
    , fixtureResolved = resolved
    , fixtureClientProcess = clientProcess
    , fixtureServerProcess = serverProcess
    }

protocolFamily :: GrammarV1ProtocolDecl -> Either String BinaryProtocolFamily
protocolFamily protocol =
  case grammarV1ClosedBinaryProtocolFamily
      protocolKey protocolInterface protocol of
    Just (Right value) -> Right value
    other -> Left ("expected closed PingRoundTrip family, got " <> show other)

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
    other -> Left ("expected checked PingRoundTrip architecture, got " <> show other)

parseSource
  :: Either String
      ( GrammarV1ProtocolDecl
      , GrammarV1ComponentDecl
      , GrammarV1ComponentDecl
      , GrammarV1ArchitectureDecl
      )
parseSource = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int009-request-reply-runtime" source
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
  [ "protocol PingRoundTrip {"
  , "  role Client = send (x : U8) then receive (reply : String) then end Done;"
  , "  role Server = receive (x : U8) then send (reply : String) then end Done;"
  , "}"
  , "component ClientWorker(endpoint : Client[PingRoundTrip], payload : U8) {"
  , "  let awaiting = send payload on endpoint;"
  , "  let (done, reply) = receive String on awaiting;"
  , "  let writeDecision = console_write(reply);"
  , "  close done;"
  , "}"
  , "component ServerWorker(endpoint : Server[PingRoundTrip]) {"
  , "  let (replyEndpoint, request) = receive U8 on endpoint;"
  , "  let done = send \"pong\" on replyEndpoint;"
  , "  close done;"
  , "}"
  , "architecture RoundTrip {"
  , "  instance client = ClientWorker;"
  , "  instance server = ServerWorker;"
  , "  process client_run = client;"
  , "  process server_run = server;"
  , "  protocol ping = PingRoundTrip;"
  , "  role ping.Client = client;"
  , "  role ping.Server = server;"
  , "  entry payload : U8;"
  , "  bind client.endpoint = ping.Client;"
  , "  bind client.payload = payload;"
  , "  bind server.endpoint = ping.Server;"
  , "}"
  , "program main = instantiate RoundTrip;"
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

stdoutCapability :: CapabilityOccurrenceKey
stdoutCapability = CapabilityOccurrenceKey "authority.console.stdout"

protocolKey, clientKey, serverKey, architectureKey :: DeclarationKey
protocolKey = DeclarationKey "protocol.ping-round-trip"
clientKey = DeclarationKey "component.ClientWorker"
serverKey = DeclarationKey "component.ServerWorker"
architectureKey = DeclarationKey "architecture.RoundTrip"

protocolInterface :: InterfaceRevision
protocolInterface = InterfaceRevision "protocol.ping-round-trip.v1"

clientRevision, serverRevision, architectureRevision :: DefinitionRevision
clientRevision = DefinitionRevision "component.ClientWorker.v1"
serverRevision = DefinitionRevision "component.ServerWorker.v1"
architectureRevision = DefinitionRevision "architecture.round-trip.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
