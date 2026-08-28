{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Context
  ( emptyContext
  , insertBinding
  )
import Phil.Core.Process
import Phil.Core.ProcessLifecycle
import Phil.Core.Protocol
import Phil.Core.Static
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-007 fatal transition leaves peer state untouched" fatalLeavesPeerUntouched
    , test "CONC-007 fatal cleanup must be explicit" fatalCleanupMustBeExplicit
    , test "CONC-007 fabricated peer endpoint progression rejects" fabricatedPeerProgressionRejects
    , test "CONC-007 fabricated peer cancellation rejects" fabricatedPeerCancellationRejects
    , test "CONC-007 terminal process cannot be re-failed" terminalProcessCannotReactivate
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

fatalLeavesPeerUntouched :: Either String ()
fatalLeavesPeerUntouched = do
  before <- baseRuntime
  let (actor, peer) = processKeys (runtimeNetwork before)
  peerBefore <- lookupContext peer before
  after <- mapLeft show $ applyFatalProcessTransition (fatalTransition actor) before
  peerAfter <- lookupContext peer after
  assert (peerAfter == peerBefore)
    "fatal actor transition changed peer protocol/resource context"
  peerStatus <- lookupStatus peer after
  assert (peerStatus == ProcessRunning)
    "fatal actor transition fabricated a peer terminal/cancellation outcome"
  assert (lookupProtocolEndpoint peerEndpoint peerAfter /= Nothing)
    "fatal actor transition implicitly closed the peer endpoint"
  actorStatus <- lookupStatus actor after
  case actorStatus of
    ProcessTerminal fact ->
      assert
        (terminalFactControl fact == Failed "fatal.actor" "boom")
        "actor terminal fact lost its exact fatal outcome"
    ProcessRunning -> Left "fatal actor remained running"
  mapLeft show $ validateFatalProcessLocality actor before after

fatalCleanupMustBeExplicit :: Either String ()
fatalCleanupMustBeExplicit = do
  before <- baseRuntime
  let (actor, _) = processKeys (runtimeNetwork before)
      incomplete = (fatalTransition actor) { fatalTransitionDisposals = [] }
  case applyFatalProcessTransition incomplete before of
    Left (FatalTerminalResourceError actual _) ->
      assert (actual == actor) "missing-disposal rejection named wrong actor"
    other -> Left ("implicit fatal cleanup was accepted: " <> show other)

fabricatedPeerProgressionRejects :: Either String ()
fabricatedPeerProgressionRejects = do
  before <- baseRuntime
  let (actor, peer) = processKeys (runtimeNetwork before)
  after <- mapLeft show $ applyFatalProcessTransition (fatalTransition actor) before
  peerBefore <- lookupContext peer after
  step <- mapLeft show $ checkProtocolAction
    (ProtocolSendRequest peerEndpoint peerSuccessor protocolInstance peerRole)
    peerBefore
  let fabricated = after
        { runtimeProtocolContexts = Map.insert peer
            (checkedProtocolContext step)
            (runtimeProtocolContexts after)
        }
  case validateFatalProcessLocality actor before fabricated of
    Left (FatalPeerContextChanged actual _ _) ->
      assert (actual == peer) "peer-progression rejection named wrong process"
    other -> Left ("fatal transition smuggled peer endpoint progression: " <> show other)

fabricatedPeerCancellationRejects :: Either String ()
fabricatedPeerCancellationRejects = do
  before <- baseRuntime
  let (actor, peer) = processKeys (runtimeNetwork before)
  after <- mapLeft show $ applyFatalProcessTransition (fatalTransition actor) before
  let fakeFact = ProcessTerminalFact peer (Failed "implicit.cancel" "actor failed")
      fabricated = after
        { runtimeStatuses = Map.insert peer (ProcessTerminal fakeFact) (runtimeStatuses after)
        }
  case validateFatalProcessLocality actor before fabricated of
    Left (FatalPeerStatusChanged actual ProcessRunning (ProcessTerminal fact)) ->
      assert
        (actual == peer && terminalFactControl fact == Failed "implicit.cancel" "actor failed")
        "peer-cancellation rejection lost exact fabricated outcome"
    other -> Left ("fatal transition fabricated peer cancellation: " <> show other)

terminalProcessCannotReactivate :: Either String ()
terminalProcessCannotReactivate = do
  before <- baseRuntime
  let (actor, _) = processKeys (runtimeNetwork before)
  after <- mapLeft show $ applyFatalProcessTransition (fatalTransition actor) before
  case applyFatalProcessTransition (fatalTransition actor) after of
    Left (RuntimeProcessAlreadyTerminal actual fact) ->
      assert
        (actual == actor && terminalFactControl fact == Failed "fatal.actor" "boom")
        "repeat-fatal rejection lost actor terminal identity"
    other -> Left ("terminal process accepted a second fatal transition: " <> show other)

baseRuntime :: Either String ProcessRuntimeState
baseRuntime = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  network <- mapLeft show $ activateRootProcesses network0
  let (actor, peer) = processKeys network
  actorResources <- mapLeft show $
    insertBinding Linear actorOwner (TyOpaque "ActorOwnedResource") emptyContext
  let actorContext = emptyProtocolContext { protocolResources = actorResources }
  peerContext <- mapLeft show $ insertProtocolEndpoint
    peerEndpoint protocolInstance peerRole peerSession emptyProtocolContext
  mapLeft show $ initializeProcessRuntime network (Map.fromList
    [ (actor, actorContext)
    , (peer, peerContext)
    ])

fatalTransition :: ProcessKey -> FatalProcessTransition
fatalTransition actor = FatalProcessTransition
  { fatalTransitionProcess = actor
  , fatalTransitionClass = "fatal.actor"
  , fatalTransitionDetail = "boom"
  , fatalTransitionDisposals = [actorOwner]
  }

lookupContext :: ProcessKey -> ProcessRuntimeState -> Either String ProtocolContext
lookupContext processKey state =
  maybe (Left "missing runtime protocol context") Right
    (Map.lookup processKey (runtimeProtocolContexts state))

lookupStatus :: ProcessKey -> ProcessRuntimeState -> Either String ProcessRuntimeStatus
lookupStatus processKey state =
  maybe (Left "missing runtime process status") Right
    (Map.lookup processKey (runtimeStatuses state))

peerSession :: Session
peerSession = Send (Name "message") TyUnit (End doneOutcome)

protocolInstance :: ProtocolInstanceRevision
protocolInstance = ProtocolInstanceRevision "protocol.conc007.v1"

peerRole :: ProtocolRoleKey
peerRole = ProtocolRoleKey "peer"

actorOwner, peerEndpoint, peerSuccessor :: Name
actorOwner = Name "actor.owner"
peerEndpoint = Name "peer.endpoint"
peerSuccessor = Name "peer.endpoint.next"

doneOutcome :: Outcome
doneOutcome = Outcome "done"

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
