{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Concurrent (threadDelay)
import Control.Monad (forever)
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
import Phil.Core.ProcessLifecycle (ProcessNetworkDisposition (..))
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol (ProtocolContext (..))
import Phil.Core.Protocol.Family
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Static
import Phil.IO.Console
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureSurface
  , grammarV1CheckedArchitectureSurface
  )
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

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--host-wait"] -> hostWait
    [] -> runControls
    _ -> putStrLn "FAIL: unexpected arguments" >> exitFailure

runControls :: IO ()
runControls = do
  results <- sequence
    [ test "INT-009 unbounded Ping executes a productive three-round prefix"
        prefixThreeIsProductive
    , test "INT-009 unbounded Ping prefix can extend without terminal fabrication"
        prefixExtendsProductively
    , test "INT-009 unbounded Ping source values reach every runtime round"
        sourceValuesReachRuntime
    , test "INT-009 unbounded Ping rejects an empty observation prefix"
        emptyPrefixRejects
    ]
  if and results then pure () else exitFailure

hostWait :: IO ()
hostWait = do
  hSetBuffering stdout LineBuffering
  case do
      fx <- sourceFixture
      authority <- stdoutAuthority
      (_, evidence) <- runPrefix fx authority 3
      assert
        (unboundedPingEvidenceDisposition evidence == NetworkCanStep)
        "host witness did not reach a productive nonterminal Phil state"
    of
      Left detail -> putStrLn ("FAIL: host setup -- " <> detail) >> exitFailure
      Right () -> do
        putStrLn "PHIL_NONTERMINAL:NetworkCanStep"
        putStrLn "HOST_SIGINT_READY"
        forever (threadDelay 1000000)

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

prefixThreeIsProductive :: Either String ()
prefixThreeIsProductive = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (afterPrefix, evidence) <- runPrefix fx authority 3
  let iterations = unboundedPingEvidenceIterations evidence
  assert (length iterations == 3)
    "three-round prefix did not execute exactly three Ping rounds"
  assert
    (map unboundedPingIterationIndex iterations == [0, 1, 2])
    "unbounded Ping iteration indexes were not exact"
  assert
    (unboundedPingEvidenceDisposition evidence == NetworkCanStep)
    "productive prefix was not classified NetworkCanStep"
  assert
    (all (not . Map.null . protocolEndpoints)
      (Map.elems (communicationProtocolContexts afterPrefix)))
    "productive prefix unexpectedly closed a live protocol endpoint"
  assertBackedgeChain iterations

prefixExtendsProductively :: Either String ()
prefixExtendsProductively = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (_, three) <- runPrefix fx authority 3
  (_, four) <- runPrefix fx authority 4
  let threeIterations = unboundedPingEvidenceIterations three
      fourIterations = unboundedPingEvidenceIterations four
  assert (take 3 fourIterations == threeIterations)
    "four-round prefix did not preserve the exact first three rounds"
  assert (length fourIterations == 4)
    "unbounded Ping could not extend to a fourth productive round"
  assert
    (unboundedPingEvidenceDisposition four == NetworkCanStep)
    "extended prefix fabricated a terminal disposition"

sourceValuesReachRuntime :: Either String ()
sourceValuesReachRuntime = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  (_, evidence) <- runPrefix fx authority 3
  let iterations = unboundedPingEvidenceIterations evidence
  assert
    (all
      ((== ScalarUIntLiteral 8 42) . unboundedPingIterationRequestValue)
      iterations)
    "runtime request value did not come from checked source"
  assert
    (all ((== "pong") . unboundedPingIterationReplyText) iterations)
    "runtime reply text did not come from checked source"
  assert
    (all
      ((== "pong")
        . checkedConsoleWriteRequestedText
        . unboundedPingIterationConsoleWrite)
      iterations)
    "checked stdout did not receive every source-derived reply"

emptyPrefixRejects :: Either String ()
emptyPrefixRejects = do
  fx <- sourceFixture
  authority <- stdoutAuthority
  case grammarV1RunUnboundedPingPrefix
      (fixtureInstance fx)
      (fixtureNetwork fx)
      (fixtureCommunication fx)
      (fixturePlan fx)
      0
      (PossessedCapability stdoutCapability)
      authority
      ConsoleWriteSucceeded of
    Left (GrammarV1UnboundedPingRuntimePrefixMustBePositive 0) -> Right ()
    other -> Left ("empty prefix did not reject exactly: " <> show other)

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

assertBackedgeChain :: [GrammarV1UnboundedPingIteration] -> Either String ()
assertBackedgeChain iterations =
  mapM_ checkPair (zip iterations (drop 1 iterations))
  where
    checkPair (previous, next) = do
      assert
        (unboundedPingIterationClientBackedgeEndpoint previous
          == unboundedPingIterationClientEntryEndpoint next)
        "client successor endpoint was not carried through the loop backedge"
      assert
        (unboundedPingIterationServerBackedgeEndpoint previous
          == unboundedPingIterationServerEntryEndpoint next)
        "server successor endpoint was not carried through the loop backedge"

stdoutAuthority :: Either String AuthorityState
stdoutAuthority = do
  let stdoutEnvironment = consoleEnvironmentStdout standardConsoleEnvironment
  capability <- mapLeft show $
    defaultConsoleAuthorityCapability stdoutCapability stdoutEnvironment
  mapLeft show (insertAuthorityCapability capability emptyAuthorityState)

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
      architecture
      "client"
      "client_run"
      clientProcess
      client
      clientHeader
      [occurrence]
  serverProvisioning <- mapLeft show $
    grammarV1ResolveArchitectureComponentProvisioning
      architecture
      "server"
      "server_run"
      serverProcess
      server
      serverHeader
      [occurrence]
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
    grammarV1ComponentProtocolContextFromActivation
      clientActivation activationState
  serverContext <- mapLeft show $
    grammarV1ComponentProtocolContextFromActivation
      serverActivation activationState
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
      emptyStaticContext
      [resolution]
      declarationKey
      revision
      component of
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
      ("expected checked unbounded Ping architecture, got " <> show other)

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
    parseGrammarV1StructuralSource "int009-unbounded-ping" source
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
  , "architecture BarePing {"
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
  , "program main = instantiate BarePing;"
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

stdoutCapability :: CapabilityOccurrenceKey
stdoutCapability = CapabilityOccurrenceKey "authority.console.stdout"

protocolKey, clientKey, serverKey, architectureKey :: DeclarationKey
protocolKey = DeclarationKey "protocol.ping-loop"
clientKey = DeclarationKey "component.ClientLoop"
serverKey = DeclarationKey "component.ServerLoop"
architectureKey = DeclarationKey "architecture.BarePing"

protocolInterface :: InterfaceRevision
protocolInterface = InterfaceRevision "protocol.ping-loop.v1"

clientRevision, serverRevision, architectureRevision :: DefinitionRevision
clientRevision = DefinitionRevision "component.ClientLoop.v1"
serverRevision = DefinitionRevision "component.ServerLoop.v1"
architectureRevision = DefinitionRevision "architecture.bare-ping.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
