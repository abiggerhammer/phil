{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessEndpointClosure
import Phil.Core.ProcessLifecycle
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session (SessionError (..))
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.BinderScope
import Phil.Surface.Syntax (SourcePoint (..), SourceSpan (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-008 Ping rendezvous closes both endpoint occurrences and root"
        pingCompletesToRootTerminal
    , test "INT-008 wrong close outcome cannot retire endpoint occurrence"
        wrongCloseOutcomeRejects
    , test "INT-008 terminal transition rejects a live Ping successor"
        terminalBeforeCloseRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

data PingFixture = PingFixture
  { fixtureInstance :: BinaryProtocolInstance
  , fixtureNetwork :: ProcessNetwork
  , fixtureCommunication :: ProcessCommunicationState
  , fixtureClientProcess :: ProcessKey
  , fixtureServerProcess :: ProcessKey
  }

pingCompletesToRootTerminal :: Either String ()
pingCompletesToRootTerminal = do
  fx <- pingFixture
  let exactInstance = binaryProtocolInstanceRevision (fixtureInstance fx)
  closedClient <- mapLeft show $ closeProcessEndpointState
    (fixtureNetwork fx)
    (fixtureCommunication fx)
    (fixtureClientProcess fx)
    clientSuccessor
    exactInstance
    clientRole
    doneOutcome
  closedBoth <- mapLeft show $ closeProcessEndpointState
    (fixtureNetwork fx)
    closedClient
    (fixtureServerProcess fx)
    serverSuccessor
    exactInstance
    serverRole
    doneOutcome
  assert (Map.null (communicationRestrictedOwners closedBoth))
    "closed Ping endpoints left stale restricted-owner occurrences"
  assert
    (all (Map.null . protocolEndpoints)
      (Map.elems (communicationProtocolContexts closedBoth)))
    "closed Ping endpoints left live protocol metadata"
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
        "root terminal fact did not cover exact Ping process population"
    other -> Left ("closed Ping network was not root-terminal: " <> show other)

wrongCloseOutcomeRejects :: Either String ()
wrongCloseOutcomeRejects = do
  fx <- pingFixture
  let exactInstance = binaryProtocolInstanceRevision (fixtureInstance fx)
  case closeProcessEndpointState
      (fixtureNetwork fx)
      (fixtureCommunication fx)
      (fixtureClientProcess fx)
      clientSuccessor
      exactInstance
      clientRole
      (Outcome "Wrong") of
    Left (EndpointClosureProtocolError actualProcess
      (ProtocolSessionError (CloseOutcomeMismatch expected actual))) -> do
        assert (actualProcess == fixtureClientProcess fx)
          "wrong-outcome diagnostic changed process identity"
        assert (expected == doneOutcome && actual == Outcome "Wrong")
          "wrong-outcome diagnostic changed exact outcomes"
    other -> Left ("wrong endpoint close outcome was not rejected exactly: " <> show other)

terminalBeforeCloseRejects :: Either String ()
terminalBeforeCloseRejects = do
  fx <- pingFixture
  runtime <- mapLeft show $ initializeProcessRuntime
    (fixtureNetwork fx)
    (communicationProtocolContexts (fixtureCommunication fx))
  case applyDeclaredTerminalTransition
      (terminalTransition (fixtureClientProcess fx)) runtime of
    Left (TerminalResourceError actualProcess _) ->
      assert (actualProcess == fixtureClientProcess fx)
        "live-endpoint terminal rejection changed process identity"
    other -> Left ("process terminated with live Ping successor endpoint: " <> show other)

pingFixture :: Either String PingFixture
pingFixture = do
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy pingFamily [] []
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [clientSite, serverSite]
  let (clientProcess, serverProcess) = processKeys network0
  clientActivation <- mapLeft show $ grammarV1ResolvedComponentActivation
    (clientProvisioning clientProcess clientProjection)
  serverActivation <- mapLeft show $ grammarV1ResolvedComponentActivation
    (serverProvisioning serverProcess serverProjection)
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
  let exactInstance = binaryProtocolInstanceRevision instanceValue
      request = SendReceiveRendezvous
        (rendezvousSide clientProcess clientEndpoint clientSuccessor exactInstance clientRole)
        (rendezvousSide serverProcess serverEndpoint serverSuccessor exactInstance serverRole)
  communication <- mapLeft show $
    checkProcessCommunicationState instanceValue network communication0 request
  pure PingFixture
    { fixtureInstance = instanceValue
    , fixtureNetwork = network
    , fixtureCommunication = communication
    , fixtureClientProcess = clientProcess
    , fixtureServerProcess = serverProcess
    }

rendezvousSide
  :: ProcessKey
  -> Name
  -> Name
  -> ProtocolInstanceRevision
  -> ProtocolRoleKey
  -> ProcessRendezvousSide
rendezvousSide processKey endpoint successor instanceRevision role =
  ProcessRendezvousSide
    { rendezvousProcess = processKey
    , rendezvousEndpoint = endpoint
    , rendezvousSuccessor = successor
    , rendezvousInstance = instanceRevision
    , rendezvousRole = role
    }

clientProvisioning
  :: ProcessKey
  -> ProtocolProjectionEvidence
  -> GrammarV1ResolvedComponentProvisioning
clientProvisioning processKey projection = GrammarV1ResolvedComponentProvisioning
  { resolvedProvisioningComponentOccurrence = "client"
  , resolvedProvisioningProcessSite = "client_run"
  , resolvedProvisioningProcessKey = processKey
  , resolvedProvisioningParameters =
      [ endpointParameter
          (DeclarationKey "component.ClientWorker")
          0 clientEndpoint "endpoint" clientEndpointOccurrence projection
      , entryParameter
          (DeclarationKey "component.ClientWorker")
          1 payloadName "payload" payloadOccurrence
      ]
  }

serverProvisioning
  :: ProcessKey
  -> ProtocolProjectionEvidence
  -> GrammarV1ResolvedComponentProvisioning
serverProvisioning processKey projection = GrammarV1ResolvedComponentProvisioning
  { resolvedProvisioningComponentOccurrence = "server"
  , resolvedProvisioningProcessSite = "server_run"
  , resolvedProvisioningProcessKey = processKey
  , resolvedProvisioningParameters =
      [ endpointParameter
          (DeclarationKey "component.ServerWorker")
          0 serverEndpoint "endpoint" serverEndpointOccurrence projection
      ]
  }

endpointParameter
  :: DeclarationKey
  -> Int
  -> Name
  -> Text
  -> ActivationOccurrenceKey
  -> ProtocolProjectionEvidence
  -> GrammarV1ProvisionedComponentParameter
endpointParameter declarationKey ordinal coreName displayName occurrence projection =
  GrammarV1ProvisionedComponentParameter
    { provisionedComponentParameterBinder =
        parameterBinder declarationKey ordinal coreName displayName
    , provisionedComponentParameterCheckedMode =
        CheckedTypeMode (TyEndpoint (protocolProjectionSession projection)) Linear
    , provisionedComponentParameterOccurrence = occurrence
    , provisionedComponentParameterSource =
        GrammarV1ComponentProvisioningProtocolEndpoint "ping" projection
    }

entryParameter
  :: DeclarationKey
  -> Int
  -> Name
  -> Text
  -> ActivationOccurrenceKey
  -> GrammarV1ProvisionedComponentParameter
entryParameter declarationKey ordinal coreName displayName occurrence =
  GrammarV1ProvisionedComponentParameter
    { provisionedComponentParameterBinder =
        parameterBinder declarationKey ordinal coreName displayName
    , provisionedComponentParameterCheckedMode = CheckedTypeMode (TyUInt 8) Unrestricted
    , provisionedComponentParameterOccurrence = occurrence
    , provisionedComponentParameterSource =
        GrammarV1ComponentProvisioningEntry "payload" (TyUInt 8)
    }

parameterBinder
  :: DeclarationKey
  -> Int
  -> Name
  -> Text
  -> GrammarV1ResolvedBinder
parameterBinder declarationKey ordinal coreName displayName = GrammarV1ResolvedBinder
  { grammarV1ResolvedBinderKey = GrammarV1BinderKey declarationKey ordinal
  , grammarV1ResolvedBinderCoreName = coreName
  , grammarV1ResolvedBinderKind = GrammarV1ComponentParameterBinder
  , grammarV1ResolvedBinderDisplayName = displayName
  , grammarV1ResolvedBinderSourceSpan = dummySpan
  }

pingFamily :: BinaryProtocolFamily
pingFamily = BinaryProtocolFamily
  { protocolFamilyDeclarationKey = DeclarationKey "protocol.Ping"
  , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.Ping.v1"
  , protocolFamilyRequirements = Set.empty
  , protocolFamilyPrimaryRole = clientRole
  , protocolFamilyPeerRole = serverRole
  , protocolFamilyPrimarySession = ProtocolTemplateSend
      (Name "x")
      (ProtocolConcreteType (TyUInt 8))
      (ProtocolTemplateEnd doneOutcome)
  }

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
      [ ArchitectureChildSpec clientSlot workerSpec
      , ArchitectureChildSpec serverSlot workerSpec
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

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "Client"
serverRole = ProtocolRoleKey "Server"

clientEndpoint, serverEndpoint, clientSuccessor, serverSuccessor, payloadName :: Name
clientEndpoint = Name "component.ClientWorker.param.0"
serverEndpoint = Name "component.ServerWorker.param.0"
clientSuccessor = Name "client.done"
serverSuccessor = Name "server.done"
payloadName = Name "component.ClientWorker.param.1"

doneOutcome :: Outcome
doneOutcome = Outcome "Done"

clientEndpointOccurrence, serverEndpointOccurrence, payloadOccurrence :: ActivationOccurrenceKey
clientEndpointOccurrence = ActivationOccurrenceKey "architecture.local-ping:ping.Client"
serverEndpointOccurrence = ActivationOccurrenceKey "architecture.local-ping:ping.Server"
payloadOccurrence = ActivationOccurrenceKey "architecture.local-ping:entry.payload"

dummySpan :: SourceSpan
dummySpan = SourceSpan dummyPoint dummyPoint

dummyPoint :: SourcePoint
dummyPoint = SourcePoint "int008-ping-terminal" 1 1 0

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
