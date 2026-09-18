{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Concurrent (newEmptyMVar, takeMVar, tryPutMVar)
import Control.Monad (void)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Authority
import Phil.Core.Callable
  ( CallableContract (..)
  , CalleeTransition (..)
  )
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement (..)
  , CallableMachineShape (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.EnvironmentObservation
  ( EnvironmentObservationKind (..)
  , EnvironmentObservationProvenance (..)
  , EnvironmentObservationRelationKey (..)
  , EnvironmentObservationSource (..)
  , EnvironmentObservationError (..)
  , checkEnvironmentObservation
  , checkedEnvironmentObservationProvenance
  , emptyEnvironmentObservationContext
  )
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessLifecycle
  ( ProcessNetworkDisposition (..)
  , RootTerminalFact (..)
  )
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol (ProtocolContext (..))
import Phil.Core.Protocol.Family
import Phil.Core.ProviderQualification
import Phil.Core.Static
import Phil.Core.Syntax (Mode (..))
import Phil.IO.Console
import Phil.IO.SignalCancellation
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureSurface
  , grammarV1CheckedArchitectureSurface
  )
import Phil.Surface.GrammarV1.InterruptiblePingRuntime
import Phil.Surface.GrammarV1.InterruptiblePingSource
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
import Phil.Surface.GrammarV1.UnboundedPingRuntime
import Phil.Surface.GrammarV1.UnboundedPingSource
import Phil.Surface.Syntax (Located (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (BufferMode (..), hSetBuffering, stdout)
import System.Posix.Signals
  ( Handler (..)
  , installHandler
  , keyboardSignal
  )

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--host-sigint-adapter"] -> hostSigintAdapter
    [] -> runControls
    _ -> putStrLn "FAIL: unexpected arguments" >> exitFailure

runControls :: IO ()
runControls = do
  results <- sequence
    [ test "INT-009 explicit cancellation source spells checked Done/close"
        explicitCancellationSourceAccepts
    , test "INT-009 cancellation source rejects a Ping substitution"
        cancellationSourcePingRejects
    , test "INT-009 ambient SIGINT observation cannot enter Phil"
        ambientSigintRejects
    , test "INT-009 SIGINT adapter requires possessed capability authority"
        missingSignalAuthorityRejects
    , test "INT-009 checked SIGINT adapter retains provider/capability/boundary/entry provenance"
        adapterProvenanceIsExact
    , test "INT-009 checked SIGINT selects Done and reaches genuine root terminal"
        checkedCancellationClosesExactly
    ]
  if and results then pure () else exitFailure

hostSigintAdapter :: IO ()
hostSigintAdapter = do
  hSetBuffering stdout LineBuffering
  signalBox <- newEmptyMVar
  _ <- installHandler keyboardSignal
    (Catch (void (tryPutMVar signalBox HostSignalSIGINT)))
    Nothing
  case prepareHostPrefix of
    Left detail -> putStrLn ("FAIL: host setup -- " <> detail) >> exitFailure
    Right (fx, authority, afterPrefix, prefixEvidence) -> do
      putStrLn "PHIL_NONTERMINAL:NetworkCanStep"
      putStrLn "SIGINT_ADAPTER_READY"
      event <- takeMVar signalBox
      case checkedCancellation authority event >>= finish fx afterPrefix prefixEvidence of
        Left detail -> putStrLn ("FAIL: SIGINT adapter -- " <> detail) >> exitFailure
        Right (_closed, shutdownEvidence, cancellation) -> do
          putStrLn "SIGINT_REIFIED:provider+capability+boundary+entry"
          assertIO
            (checkedSignalCancellationEvent cancellation == HostSignalSIGINT)
            "reified cancellation changed host signal identity"
          assertIO
            (Map.keysSet
              (rootTerminalProcesses
                (interruptiblePingTerminalFact shutdownEvidence))
              == Map.keysSet (processNetworkPopulation (fixtureNetwork fx)))
            "host shutdown root terminal did not cover the process population"
          putStrLn "PHIL_TERMINAL:Done"

prepareHostPrefix
  :: Either
      String
      ( Fixture
      , AuthorityState
      , ProcessCommunicationState
      , GrammarV1UnboundedPingRuntimeEvidence
      )
prepareHostPrefix = do
  fx <- sourceFixture
  _ <- interruptibleSourceFixture
  authority <- stdoutAndSignalAuthority
  (afterPrefix, evidence) <- runPrefix fx authority 3
  assert
    (unboundedPingEvidenceDisposition evidence == NetworkCanStep)
    "host witness did not reach NetworkCanStep before SIGINT"
  Right (fx, authority, afterPrefix, evidence)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

data Fixture = Fixture
  { fixtureInstance :: BinaryProtocolInstance
  , fixtureNetwork :: ProcessNetwork
  , fixtureCommunication :: ProcessCommunicationState
  , fixturePlan :: GrammarV1UnboundedPingRuntimePlan
  }

explicitCancellationSourceAccepts :: Either String ()
explicitCancellationSourceAccepts = void interruptibleSourceFixture

cancellationSourcePingRejects :: Either String ()
cancellationSourcePingRejects = do
  component <- parseInterruptibleComponent
    (Text.replace "select Done on endpoint" "select Ping on endpoint"
      interruptibleSource)
  case grammarV1CheckedInterruptiblePingSource cancelComponentKey component of
    Just (Left (GrammarV1InterruptiblePingBodyShape
      "cancellation branch must select Done")) -> Right ()
    other -> Left ("Ping substitution did not reject exactly: " <> show other)

ambientSigintRejects :: Either String ()
ambientSigintRejects =
  case checkEnvironmentObservation
      sigintKind
      (AmbientEnvironmentObservation sigintKind)
      emptyEnvironmentObservationContext of
    Left (EnvironmentObservationSourceNotExplicit
      (AmbientEnvironmentObservation actual))
        | actual == sigintKind -> Right ()
    other -> Left ("ambient SIGINT observation was admitted: " <> show other)

missingSignalAuthorityRejects :: Either String ()
missingSignalAuthorityRejects = do
  provider <- signalProviderQualification
  case checkSignalCancellationAdapter
      signalAdapterSpec
      provider
      signalOperation
      signalRequirement
      (PossessedCapability signalCapabilityOccurrence)
      emptyAuthorityState
      HostSignalSIGINT of
    Left (SignalCancellationAuthorityError
      (UnknownCapabilityOccurrence occurrence))
        | occurrence == signalCapabilityOccurrence -> Right ()
    other -> Left ("missing SIGINT authority did not reject exactly: " <> show other)

adapterProvenanceIsExact :: Either String ()
adapterProvenanceIsExact = do
  authority <- signalAuthority
  cancellation <- checkedCancellation authority HostSignalSIGINT
  assert
    (checkedEnvironmentObservationProvenance
      (checkedSignalCancellationProviderObservation cancellation)
      == EnvironmentProviderProvenance
          signalProviderRevision signalImplementationRevision signalOperation)
    "SIGINT adapter lost exact provider provenance"
  assert
    (checkedEnvironmentObservationProvenance
      (checkedSignalCancellationCapabilityObservation cancellation)
      == EnvironmentCapabilityProvenance
          signalAuthorityContract signalAuthoritySubject signalAuthorityOperation)
    "SIGINT adapter lost exact capability provenance"
  assert
    (checkedEnvironmentObservationProvenance
      (checkedSignalCancellationBoundaryObservation cancellation)
      == EnvironmentBoundaryProvenance "boundary.sigint.adapter.v1")
    "SIGINT adapter lost exact boundary provenance"
  assert
    (checkedEnvironmentObservationProvenance
      (checkedSignalCancellationEntryObservation cancellation)
      == EnvironmentEntryProvenance "entry.cancelled")
    "SIGINT adapter lost exact entry provenance"

checkedCancellationClosesExactly :: Either String ()
checkedCancellationClosesExactly = do
  fx <- sourceFixture
  _ <- interruptibleSourceFixture
  authority <- stdoutAndSignalAuthority
  (afterPrefix, prefixEvidence) <- runPrefix fx authority 3
  cancellation <- checkedCancellation authority HostSignalSIGINT
  (closed, shutdownEvidence, _) <- finish fx afterPrefix prefixEvidence cancellation
  assert
    (all (Map.null . protocolEndpoints)
      (Map.elems (communicationProtocolContexts closed)))
    "checked cancellation left live protocol endpoints"
  assert
    (Map.null (communicationRestrictedOwners closed))
    "checked cancellation left restricted owners"
  assert
    (Map.keysSet
      (rootTerminalProcesses (interruptiblePingTerminalFact shutdownEvidence))
      == Map.keysSet (processNetworkPopulation (fixtureNetwork fx)))
    "checked cancellation did not produce a complete root terminal fact"

finish
  :: Fixture
  -> ProcessCommunicationState
  -> GrammarV1UnboundedPingRuntimeEvidence
  -> CheckedSignalCancellation
  -> Either
      String
      ( ProcessCommunicationState
      , GrammarV1InterruptiblePingEvidence
      , CheckedSignalCancellation
      )
finish fx afterPrefix prefixEvidence cancellation = do
  (closed, shutdownEvidence) <- mapLeft show $
    grammarV1FinishUnboundedPingOnCancellation
      (fixtureInstance fx)
      (fixtureNetwork fx)
      afterPrefix
      (fixturePlan fx)
      prefixEvidence
      cancellation
  Right (closed, shutdownEvidence, cancellation)

checkedCancellation
  :: AuthorityState
  -> HostSignalEvent
  -> Either String CheckedSignalCancellation
checkedCancellation authority event = do
  provider <- signalProviderQualification
  mapLeft show $
    checkSignalCancellationAdapter
      signalAdapterSpec
      provider
      signalOperation
      signalRequirement
      (PossessedCapability signalCapabilityOccurrence)
      authority
      event

runPrefix
  :: Fixture
  -> AuthorityState
  -> Int
  -> Either
      String
      (ProcessCommunicationState, GrammarV1UnboundedPingRuntimeEvidence)
runPrefix fx authority rounds = mapLeft show $
  grammarV1RunUnboundedPingPrefix
    (fixtureInstance fx)
    (fixtureNetwork fx)
    (fixtureCommunication fx)
    (fixturePlan fx)
    rounds
    (PossessedCapability stdoutCapability)
    authority
    ConsoleWriteSucceeded

stdoutAndSignalAuthority :: Either String AuthorityState
stdoutAndSignalAuthority = do
  withStdout <- stdoutAuthority
  mapLeft show $ insertAuthorityCapability signalCapability withStdout

stdoutAuthority :: Either String AuthorityState
stdoutAuthority = do
  let stdoutEnvironment = consoleEnvironmentStdout standardConsoleEnvironment
  capability <- mapLeft show $
    defaultConsoleAuthorityCapability stdoutCapability stdoutEnvironment
  mapLeft show $ insertAuthorityCapability capability emptyAuthorityState

signalAuthority :: Either String AuthorityState
signalAuthority =
  mapLeft show $ insertAuthorityCapability signalCapability emptyAuthorityState

interruptibleSourceFixture
  :: Either String GrammarV1CheckedInterruptiblePingSource
interruptibleSourceFixture = do
  component <- parseInterruptibleComponent interruptibleSource
  case grammarV1CheckedInterruptiblePingSource cancelComponentKey component of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked interruptible Ping source, got " <> show other)

parseInterruptibleComponent
  :: Text
  -> Either String GrammarV1ComponentDecl
parseInterruptibleComponent input = do
  parsed <- mapLeft show $
    parseGrammarV1StructuralSource "int009-interruptible-ping-source" input
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> declarationAsComponent "CancelOnSignal" top
    declarations -> Left
      ("expected one interruptible component, got "
        <> show (length declarations) <> " declarations")

interruptibleSource :: Text
interruptibleSource = Text.unlines
  [ "component CancelOnSignal(endpoint : Client[PingLoop], cancelled : Bool) {"
  , "  if cancelled {"
  , "    let done = select Done on endpoint;"
  , "    close done;"
  , "  };"
  , "}"
  ]

sourceFixture :: Either String Fixture
sourceFixture = do
  (protocol, client, server, architectureDecl) <- parseSource
  family <- protocolFamily protocol
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  let resolution = GrammarV1ProtocolEndpointResolution
        { protocolEndpointResolutionSourceReference =
            ReferencedGenericStaticActual "PingLoop"
        , protocolEndpointResolutionInstance = instanceValue
        }
      occurrence = GrammarV1ArchitectureProtocolOccurrence
        { architectureProtocolOccurrenceName = "ping"
        , architectureProtocolOccurrenceSourceReference =
            ReferencedGenericStaticActual "PingLoop"
        , architectureProtocolOccurrenceInstance = instanceValue
        }
  clientHeader <- semanticHeader clientKey clientRevision resolution client
  serverHeader <- semanticHeader serverKey serverRevision resolution server
  checkedSource <- case grammarV1CheckedUnboundedPingSource
      clientKey client serverKey server of
    Just (Right value) -> Right value
    other -> Left ("expected checked unbounded Ping source, got " <> show other)
  architecture <- checkedArchitecture architectureDecl
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [clientSite, serverSite]
  let (clientProcess, serverProcess) = processKeys network0
  clientProvisioning <- mapLeft show $
    grammarV1ResolveArchitectureComponentProvisioning
      architecture "client" "client_run" clientProcess client clientHeader [occurrence]
  serverProvisioning <- mapLeft show $
    grammarV1ResolveArchitectureComponentProvisioning
      architecture "server" "server_run" serverProcess server serverHeader [occurrence]
  plan <- mapLeft show $
    grammarV1ResolveUnboundedPingRuntime
      checkedSource clientProvisioning serverProvisioning
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
    , fixturePlan = plan
    }

protocolFamily :: GrammarV1ProtocolDecl -> Either String BinaryProtocolFamily
protocolFamily protocol =
  case grammarV1ClosedBinaryProtocolFamily protocolKey protocolInterface protocol of
    Just (Right value) -> Right value
    other -> Left ("expected closed recursive PingLoop family, got " <> show other)

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
    other -> Left
      ("expected endpoint-aware component header, got " <> show other)

checkedArchitecture
  :: GrammarV1ArchitectureDecl
  -> Either String GrammarV1CheckedArchitectureSurface
checkedArchitecture architectureDecl =
  case grammarV1CheckedArchitectureSurface
      emptyStaticContext architectureKey architectureRevision architectureDecl of
    Just (Right value) -> Right value
    other -> Left
      ("expected checked interruptible Ping architecture, got " <> show other)

parseSource
  :: Either
      String
      ( GrammarV1ProtocolDecl
      , GrammarV1ComponentDecl
      , GrammarV1ComponentDecl
      , GrammarV1ArchitectureDecl
      )
parseSource = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int009-interruptible-ping" source
  case grammarV1TopLevelDecls sourceFile of
    [ Located _ protocolTop
      , Located _ clientTop
      , Located _ serverTop
      , Located _ architectureTop
      , Located _ programTop
      ] -> do
        protocol <- declarationAsProtocol protocolTop
        client <- declarationAsComponent "ClientLoop" clientTop
        server <- declarationAsComponent "ServerLoop" serverTop
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
  [ "protocol PingLoop {"
  , "  role Client = recursive Loop = select {"
  , "    Ping => send (x : U8) then receive (reply : String) then continue Loop |"
  , "    Done => end Done"
  , "  };"
  , "  role Server = recursive Loop = offer {"
  , "    Ping => receive (x : U8) then send (reply : String) then continue Loop |"
  , "    Done => end Done"
  , "  };"
  , "}"
  , "component ClientLoop(endpoint : Client[PingLoop]) {"
  , "  loop state (currentEndpoint = endpoint) {"
  , "    let selected = select Ping on currentEndpoint;"
  , "    let awaiting = send 42 on selected;"
  , "    let (nextEndpoint, reply) = receive String on awaiting;"
  , "    let writeDecision = console_write(reply);"
  , "    continue (nextEndpoint);"
  , "  };"
  , "}"
  , "component ServerLoop(endpoint : Server[PingLoop]) {"
  , "  loop state (currentEndpoint = endpoint) {"
  , "    let (replyEndpoint, request) = receive U8 on currentEndpoint;"
  , "    let nextEndpoint = send \"pong\" on replyEndpoint;"
  , "    continue (nextEndpoint);"
  , "  };"
  , "}"
  , "architecture InterruptiblePing {"
  , "  instance client = ClientLoop;"
  , "  instance server = ServerLoop;"
  , "  process client_run = client;"
  , "  process server_run = server;"
  , "  protocol ping = PingLoop;"
  , "  role ping.Client = client;"
  , "  role ping.Server = server;"
  , "  bind client.endpoint = ping.Client;"
  , "  bind server.endpoint = ping.Server;"
  , "}"
  , "program main = instantiate InterruptiblePing;"
  ]

declarationAsProtocol
  :: GrammarV1TopLevelDecl
  -> Either String GrammarV1ProtocolDecl
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
clientWorkerSpec = leafSpec "ClientLoop"
serverWorkerSpec = leafSpec "ServerLoop"

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

stdoutCapability, signalCapabilityOccurrence :: CapabilityOccurrenceKey
stdoutCapability = CapabilityOccurrenceKey "authority.console.stdout"
signalCapabilityOccurrence = CapabilityOccurrenceKey "authority.signal.sigint"

protocolKey, clientKey, serverKey, cancelComponentKey, architectureKey
  :: DeclarationKey
protocolKey = DeclarationKey "protocol.ping-loop"
clientKey = DeclarationKey "component.ClientLoop"
serverKey = DeclarationKey "component.ServerLoop"
cancelComponentKey = DeclarationKey "component.CancelOnSignal"
architectureKey = DeclarationKey "architecture.InterruptiblePing"

protocolInterface :: InterfaceRevision
protocolInterface = InterfaceRevision "protocol.ping-loop.v1"

clientRevision, serverRevision, architectureRevision :: DefinitionRevision
clientRevision = DefinitionRevision "component.ClientLoop.v1"
serverRevision = DefinitionRevision "component.ServerLoop.v1"
architectureRevision = DefinitionRevision "architecture.interruptible-ping.v1"

sigintKind :: EnvironmentObservationKind
sigintKind = EnvironmentOtherObservation "signal.SIGINT"

signalAdapterSpec :: SignalCancellationAdapterSpec
signalAdapterSpec = SignalCancellationAdapterSpec
  { signalCancellationProviderRelation =
      EnvironmentObservationRelationKey "int009.sigint.provider"
  , signalCancellationCapabilityRelation =
      EnvironmentObservationRelationKey "int009.sigint.capability"
  , signalCancellationBoundaryRelation =
      EnvironmentObservationRelationKey "int009.sigint.boundary"
  , signalCancellationEntryRelation =
      EnvironmentObservationRelationKey "int009.sigint.entry"
  , signalCancellationBoundaryIdentity = "boundary.sigint.adapter.v1"
  , signalCancellationEntryIdentity = "entry.cancelled"
  }

signalProviderRevision :: InterfaceRevision
signalProviderRevision = InterfaceRevision "int009.signal.provider.v1"

signalImplementationRevision :: DefinitionRevision
signalImplementationRevision = DefinitionRevision "int009.signal.impl.v1"

signalOperation :: ProviderOperationKey
signalOperation = ProviderOperationKey "signal.observe.sigint"

signalEntry :: ProviderImplementationEntryKey
signalEntry = ProviderImplementationEntryKey "impl.signal.observe.sigint"

signalContractOutcome, signalImplementationOutcome :: ProviderOutcomeKey
signalContractOutcome = ProviderOutcomeKey "signal.observed"
signalImplementationOutcome = ProviderOutcomeKey "impl.signal.observed"

emptyResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue
  Set.empty Set.empty Set.empty Set.empty Set.empty

signalSurface :: CallableRefinementSurface
signalSurface = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "signal.observe.sigint()->Bool"
  , callableRefinementContract = CallableContract
      (InterfaceRevision "int009.signal.call.v1")
      PreserveCallee
      Set.empty
  , callableRefinementCallerAuthority = Set.singleton
      (CallableAuthorityRequirement "signal.observe.sigint")
  , callableRefinementFailures = Set.empty
  }

signalProviderContract :: ProviderContract
signalProviderContract = ProviderContract
  signalProviderRevision
  (Map.singleton signalOperation ProviderOperationContract
    { providerOperationCallableContract = signalSurface
    , providerOperationPreconditions = Set.empty
    , providerOperationOutcomeResidues =
        Map.singleton signalContractOutcome emptyResidue
    })

signalProviderImplementation :: ProviderImplementation
signalProviderImplementation = ProviderImplementation
  { providerImplementationDefinitionRevision = signalImplementationRevision
  , providerImplementationEntries =
      Map.singleton signalEntry ProviderImplementationOperation
        { providerImplementationCallable = signalSurface
        , providerImplementationPreconditions = Set.empty
        , providerImplementationOutcomeResidues =
            Map.singleton signalImplementationOutcome emptyResidue
        }
  , providerImplementationSymbols = Set.singleton "sigaction(SIGINT)"
  }

signalProviderClaim :: ProviderQualificationClaim
signalProviderClaim = ProviderQualificationClaim
  { providerQualificationRequiredInterface = signalProviderRevision
  , providerQualificationImplementationRevision = signalImplementationRevision
  , providerQualificationOperationCorrespondences =
      Map.singleton signalOperation ProviderOperationCorrespondence
        { providerCorrespondenceImplementationEntry = signalEntry
        , providerCorrespondenceOutcomes =
            Map.singleton signalImplementationOutcome signalContractOutcome
        }
  }

signalProviderQualification :: Either String CheckedProviderSemanticQualification
signalProviderQualification = mapLeft show $
  checkProviderSemanticQualification
    signalProviderContract signalProviderImplementation signalProviderClaim

signalAuthorityContract :: AuthorityContractKey
signalAuthorityContract = AuthorityContractKey "int009.signal.authority.v1"

signalAuthoritySubject :: AuthoritySubjectKey
signalAuthoritySubject = AuthoritySubjectKey "host.signal.SIGINT"

signalAuthorityOperation :: AuthorityOperationKey
signalAuthorityOperation = AuthorityOperationKey "observe"

signalRequirement :: AuthorityRequirement
signalRequirement = AuthorityRequirement
  signalAuthorityContract signalAuthoritySubject signalAuthorityOperation

signalCapability :: AuthorityCapability
signalCapability = AuthorityCapability
  { authorityCapabilityOccurrence = signalCapabilityOccurrence
  , authorityCapabilityContract = signalAuthorityContract
  , authorityCapabilitySubject = signalAuthoritySubject
  , authorityCapabilityMode = Unrestricted
  , authorityCapabilityOperations = Set.singleton signalAuthorityOperation
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

assertIO :: Bool -> String -> IO ()
assertIO condition detail
  | condition = pure ()
  | otherwise = putStrLn ("FAIL: " <> detail) >> exitFailure

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
