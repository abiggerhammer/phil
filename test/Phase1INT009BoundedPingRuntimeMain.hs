{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
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
import Phil.Core.ProcessLifecycle (RootTerminalFact (..))
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol (ProtocolContext (..))
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
import Phil.Surface.GrammarV1.BoundedPingLoopSource
import Phil.Surface.GrammarV1.BoundedPingRuntime
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
    [ test "INT-009 bounded Ping count=3 performs exactly three replies then closes"
        countThreeRunsAndTerminates
    , test "INT-009 bounded Ping count=0 selects Done without a Ping round"
        countZeroTerminatesImmediately
    , test "INT-009 bounded Ping retains exact loop-state and count-entry identity"
        loopAndCountIdentityAreExact
    , test "INT-009 bounded Ping rejects the wrong root count occurrence"
        wrongCountOccurrenceRejects
    , test "INT-009 bounded Ping rejects a non-U32 runtime count"
        wrongCountWidthRejects
    , test "INT-009 bounded Ping output requires possessed stdout authority"
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
  , fixturePlan :: GrammarV1BoundedPingRuntimePlan
  }

countThreeRunsAndTerminates :: Either String ()
countThreeRunsAndTerminates = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (closed, evidence) <- runWithCount fx authority (ScalarUIntLiteral 32 3)
  let rounds = boundedPingEvidenceIterations evidence
  assert (length rounds == 3) "count=3 did not execute exactly three Ping rounds"
  assert (map boundedPingIterationRemainingBefore rounds == [3,2,1])
    "bounded Ping did not preserve exact pre-decrement counts"
  assert (map boundedPingIterationRemainingAfter rounds == [2,1,0])
    "bounded Ping did not prove exact decrement sequence"
  assert (all ((== ScalarUIntLiteral 8 42) . boundedPingIterationRequestValue) rounds)
    "bounded Ping changed the concrete request value"
  assert (all ((== "pong") . boundedPingIterationReplyText) rounds)
    "bounded Ping changed the concrete reply value"
  assert (all ((== "pong") . checkedConsoleWriteRequestedText
      . boundedPingIterationConsoleWrite) rounds)
    "bounded Ping did not write each exact received reply"
  assert (all ((== ConsoleWriteSucceeded) . checkedConsoleWriteOutcome
      . boundedPingIterationConsoleWrite) rounds)
    "bounded Ping did not retain successful output outcomes"
  assertBackedgeChain rounds
  assertClosedAndTerminal fx closed evidence

countZeroTerminatesImmediately :: Either String ()
countZeroTerminatesImmediately = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (closed, evidence) <- runWithCount fx authority (ScalarUIntLiteral 32 0)
  assert (null (boundedPingEvidenceIterations evidence))
    "count=0 executed a Ping round before selecting Done"
  assertClosedAndTerminal fx closed evidence

loopAndCountIdentityAreExact :: Either String ()
loopAndCountIdentityAreExact = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (_, evidence) <- runWithCount fx authority (ScalarUIntLiteral 32 3)
  let plan = fixturePlan fx
      loopSource = boundedPingRuntimeLoopSource plan
  assert
    (boundedPingEvidenceEndpointStateBinder evidence == boundedPingEndpointState loopSource)
    "runtime evidence changed the exact endpoint loop-state binder"
  assert
    (boundedPingEvidenceCountStateBinder evidence == boundedPingCountState loopSource)
    "runtime evidence changed the exact count loop-state binder"
  assert
    (boundedPingEvidenceCountOccurrence evidence == boundedPingRuntimeCountOccurrence plan)
    "runtime evidence changed the exact root count occurrence"
  assert (boundedPingEvidenceInitialCount evidence == 3)
    "runtime evidence changed the concrete initial count"

wrongCountOccurrenceRejects :: Either String ()
wrongCountOccurrenceRejects = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  let bad = GrammarV1RootCountValue
        (ActivationOccurrenceKey "wrong-count-entry")
        (ScalarUIntLiteral 32 3)
  case grammarV1RunBoundedPing
      (fixtureInstance fx) (fixtureNetwork fx) (fixtureCommunication fx)
      (fixturePlan fx) bad (ScalarUIntLiteral 8 42) "pong"
      (PossessedCapability stdoutCapability) authority ConsoleWriteSucceeded of
    Left (GrammarV1BoundedPingRuntimeCountOccurrenceMismatch expected actual) -> do
      assert (expected == boundedPingRuntimeCountOccurrence (fixturePlan fx))
        "count occurrence rejection changed expected identity"
      assert (actual == ActivationOccurrenceKey "wrong-count-entry")
        "count occurrence rejection changed actual identity"
    other -> Left ("wrong count occurrence did not reject exactly: " <> show other)

wrongCountWidthRejects :: Either String ()
wrongCountWidthRejects = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  let bad = GrammarV1RootCountValue
        (boundedPingRuntimeCountOccurrence (fixturePlan fx))
        (ScalarUIntLiteral 16 3)
  case grammarV1RunBoundedPing
      (fixtureInstance fx) (fixtureNetwork fx) (fixtureCommunication fx)
      (fixturePlan fx) bad (ScalarUIntLiteral 8 42) "pong"
      (PossessedCapability stdoutCapability) authority ConsoleWriteSucceeded of
    Left (GrammarV1BoundedPingRuntimeScalarTypeMismatch (TyUInt 32) (TyUInt 16)) -> Right ()
    other -> Left ("wrong count width did not reject exactly: " <> show other)

missingStdoutAuthorityRejects :: Either String ()
missingStdoutAuthorityRejects = do
  fx <- sourceFixture
  let countInput = GrammarV1RootCountValue
        (boundedPingRuntimeCountOccurrence (fixturePlan fx))
        (ScalarUIntLiteral 32 1)
  case grammarV1RunBoundedPing
      (fixtureInstance fx) (fixtureNetwork fx) (fixtureCommunication fx)
      (fixturePlan fx) countInput (ScalarUIntLiteral 8 42) "pong"
      (PossessedCapability stdoutCapability) emptyAuthorityState ConsoleWriteSucceeded of
    Left (GrammarV1BoundedPingRuntimeConsoleError _) -> Right ()
    other -> Left ("missing stdout authority did not reject output: " <> show other)

runWithCount
  :: Fixture
  -> AuthorityState
  -> ScalarLiteral
  -> Either String (ProcessCommunicationState, GrammarV1BoundedPingRuntimeEvidence)
runWithCount fx authority countValue = mapLeft show $ grammarV1RunBoundedPing
  (fixtureInstance fx)
  (fixtureNetwork fx)
  (fixtureCommunication fx)
  (fixturePlan fx)
  GrammarV1RootCountValue
    { rootCountOccurrence = boundedPingRuntimeCountOccurrence (fixturePlan fx)
    , rootCountValue = countValue
    }
  (ScalarUIntLiteral 8 42)
  "pong"
  (PossessedCapability stdoutCapability)
  authority
  ConsoleWriteSucceeded

assertBackedgeChain :: [GrammarV1BoundedPingIteration] -> Either String ()
assertBackedgeChain rounds = mapM_ checkPair (zip rounds (drop 1 rounds))
  where
    checkPair (previous, next) = do
      assert
        (boundedPingIterationClientBackedgeEndpoint previous
          == boundedPingIterationClientEntryEndpoint next)
        "client fresh successor was not carried through the loop backedge"
      assert
        (boundedPingIterationServerBackedgeEndpoint previous
          == boundedPingIterationServerEntryEndpoint next)
        "server fresh successor was not carried through the loop backedge"

assertClosedAndTerminal
  :: Fixture
  -> ProcessCommunicationState
  -> GrammarV1BoundedPingRuntimeEvidence
  -> Either String ()
assertClosedAndTerminal fx closed evidence = do
  assert (Map.null (communicationRestrictedOwners closed))
    "bounded Ping terminal close left restricted owners"
  assert
    (all (Map.null . protocolEndpoints)
      (Map.elems (communicationProtocolContexts closed)))
    "bounded Ping terminal close left protocol endpoints"
  let terminal = boundedPingEvidenceTerminalFact evidence
  assert
    (Map.keysSet (rootTerminalProcesses terminal)
      == Map.keysSet (processNetworkPopulation (fixtureNetwork fx)))
    "bounded Ping root terminal fact did not cover the process population"

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
        { protocolEndpointResolutionSourceReference = ReferencedGenericStaticActual "PingCount"
        , protocolEndpointResolutionInstance = instanceValue
        }
      occurrence = GrammarV1ArchitectureProtocolOccurrence
        { architectureProtocolOccurrenceName = "ping"
        , architectureProtocolOccurrenceSourceReference = ReferencedGenericStaticActual "PingCount"
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
  loopSource <- case grammarV1CheckedBoundedPingLoop clientKey client of
    Just (Right value) -> Right value
    other -> Left ("expected checked bounded Ping loop source, got " <> show other)
  plan <- mapLeft show $
    grammarV1ResolveBoundedPingRuntime loopSource clientProvisioning serverProvisioning
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
    other -> Left ("expected closed recursive PingCount family, got " <> show other)

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
    other -> Left ("expected checked bounded Ping architecture, got " <> show other)

parseSource
  :: Either String
      ( GrammarV1ProtocolDecl
      , GrammarV1ComponentDecl
      , GrammarV1ComponentDecl
      , GrammarV1ArchitectureDecl
      )
parseSource = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int009-bounded-ping-runtime" source
  case grammarV1TopLevelDecls sourceFile of
    [ Located _ protocolTop
      , Located _ clientTop
      , Located _ serverTop
      , Located _ architectureTop
      , Located _ programTop
      ] -> do
        protocol <- declarationAsProtocol protocolTop
        client <- declarationAsComponent "ClientCounter" clientTop
        server <- declarationAsComponent "ServerCounter" serverTop
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
  [ "protocol PingCount {"
  , "  role Client = recursive Loop = select {"
  , "    Ping => send (x : U8) then receive (reply : String) then continue Loop |"
  , "    Done => end Done"
  , "  };"
  , "  role Server = recursive Loop = offer {"
  , "    Ping => receive (x : U8) then send (reply : String) then continue Loop |"
  , "    Done => end Done"
  , "  };"
  , "}"
  , "component ClientCounter(endpoint : Client[PingCount], count : U32) {"
  , "  loop state (currentEndpoint = endpoint, remaining : U32 = count) {"
  , "    continue (currentEndpoint, remaining);"
  , "  };"
  , "}"
  , "component ServerCounter(endpoint : Server[PingCount]) {}"
  , "architecture BoundedPing {"
  , "  instance client = ClientCounter;"
  , "  instance server = ServerCounter;"
  , "  process client_run = client;"
  , "  process server_run = server;"
  , "  protocol ping = PingCount;"
  , "  role ping.Client = client;"
  , "  role ping.Server = server;"
  , "  entry count : U32;"
  , "  bind client.endpoint = ping.Client;"
  , "  bind client.count = count;"
  , "  bind server.endpoint = ping.Server;"
  , "}"
  , "program main = instantiate BoundedPing;"
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
clientWorkerSpec = leafSpec "ClientCounter"
serverWorkerSpec = leafSpec "ServerCounter"

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
protocolKey = DeclarationKey "protocol.ping-count"
clientKey = DeclarationKey "component.ClientCounter"
serverKey = DeclarationKey "component.ServerCounter"
architectureKey = DeclarationKey "architecture.BoundedPing"

protocolInterface :: InterfaceRevision
protocolInterface = InterfaceRevision "protocol.ping-count.v1"

clientRevision, serverRevision, architectureRevision :: DefinitionRevision
clientRevision = DefinitionRevision "component.ClientCounter.v1"
serverRevision = DefinitionRevision "component.ServerCounter.v1"
architectureRevision = DefinitionRevision "architecture.bounded-ping.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
