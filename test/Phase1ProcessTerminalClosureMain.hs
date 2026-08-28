{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Context
  ( CheckError (..)
  , emptyContext
  , insertBinding
  , startSharedLoan
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
    [ test "CONC-008 all process terminal facts close root" allProcessesCloseRoot
    , test "CONC-008 one finished process with blocked peer is stuck" blockedPeerIsStuck
    , test "CONC-008 live linear resource blocks terminal fact" liveLinearResourceRejects
    , test "CONC-008 live shared loan blocks terminal fact" liveLoanRejects
    , test "CONC-008 live endpoint blocks terminal fact" liveEndpointRejects
    , test "CONC-008 live residual obligation blocks declared terminal fact" liveObligationRejects
    , test "CONC-008 live residual obligation blocks fatal terminal fact" fatalLiveObligationRejects
    , test "CONC-008 root residue blocks whole-program closure" rootResidueRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

allProcessesCloseRoot :: Either String ()
allProcessesCloseRoot = do
  before <- baseRuntime
  let (processA, processB) = processKeys (runtimeNetwork before)
  afterA <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition processA) before
  afterB <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition processB) afterA
  disposition <- mapLeft show $ classifyProcessNetwork emptyRootClosure [] afterB
  case disposition of
    NetworkTerminal fact -> do
      assert
        (Map.keysSet (rootTerminalProcesses fact) == Set.fromList [processA, processB])
        "root terminal fact did not contain the exact process population"
      assert
        (all ((== Closed doneOutcome) . terminalFactControl)
          (Map.elems (rootTerminalProcesses fact)))
        "root terminal fact changed a process terminal outcome"
    other -> Left ("all-process closure did not produce root terminal fact: " <> show other)

blockedPeerIsStuck :: Either String ()
blockedPeerIsStuck = do
  before <- baseRuntime
  let (processA, processB) = processKeys (runtimeNetwork before)
  afterA <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition processA) before
  disposition <- mapLeft show $ classifyProcessNetwork emptyRootClosure [] afterA
  case disposition of
    NetworkStuck active ->
      assert (active == Set.singleton processB)
        "stuck classification did not identify the exact blocked active peer"
    other -> Left ("one-process/main-worker completion was treated as success: " <> show other)

liveLinearResourceRejects :: Either String ()
liveLinearResourceRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
  resources <- mapLeft show $
    insertBinding Linear ownerName (TyOpaque "OwnedResource") emptyContext
  runtime <- mapLeft show $ initializeProcessRuntime network (Map.fromList
    [ (processA, emptyProtocolContext { protocolResources = resources })
    , (processB, emptyProtocolContext)
    ])
  case applyDeclaredTerminalTransition (terminalTransition processA) runtime of
    Left (TerminalResourceError actual (UnconsumedLinearResources residue)) ->
      assert (actual == processA && Map.member ownerName residue)
        "live-resource terminal rejection lost exact owner/process identity"
    other -> Left ("live linear resource did not block terminal fact: " <> show other)

liveLoanRejects :: Either String ()
liveLoanRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
  resources0 <- mapLeft show $
    insertBinding Linear loanOwnerName (TyOpaque "LoanedOwner") emptyContext
  resources <- mapLeft show $ startSharedLoan loanOwnerName resources0
  runtime <- mapLeft show $ initializeProcessRuntime network (Map.fromList
    [ (processA, emptyProtocolContext { protocolResources = resources })
    , (processB, emptyProtocolContext)
    ])
  case applyDeclaredTerminalTransition (terminalTransition processA) runtime of
    Left (TerminalResourceError actual (EscapingLoans loans)) ->
      assert (actual == processA && loans == Set.singleton loanOwnerName)
        "live-loan terminal rejection lost exact loan/process identity"
    other -> Left ("live shared loan did not block terminal fact: " <> show other)

liveEndpointRejects :: Either String ()
liveEndpointRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      endpointBinding = ProtocolEndpointBinding
        { protocolEndpointName = endpointName
        , protocolEndpointInstance = ProtocolInstanceRevision "protocol.conc008.v1"
        , protocolEndpointRole = ProtocolRoleKey "worker"
        , protocolEndpointSession = End doneOutcome
        }
      endpointContext = emptyProtocolContext
        { protocolEndpoints = Map.singleton endpointName endpointBinding }
  runtime <- mapLeft show $ initializeProcessRuntime network (Map.fromList
    [ (processA, endpointContext)
    , (processB, emptyProtocolContext)
    ])
  case applyDeclaredTerminalTransition (terminalTransition processA) runtime of
    Left (TerminalLiveEndpoints actual endpoints) ->
      assert (actual == processA && endpoints == [endpointName])
        "live-endpoint terminal rejection lost exact endpoint/process identity"
    other -> Left ("live endpoint did not block terminal fact: " <> show other)

liveObligationRejects :: Either String ()
liveObligationRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      obligation = ObligationId "obligation.conc008.local"
  runtime <- mapLeft show $ initializeProcessRuntimeWithObligations
    network
    (Map.fromList [(processA, emptyProtocolContext), (processB, emptyProtocolContext)])
    (Map.singleton processA (Set.singleton obligation))
  case applyDeclaredTerminalTransition (terminalTransition processA) runtime of
    Left (TerminalOpenObligations actual obligations) ->
      assert (actual == processA && obligations == Set.singleton obligation)
        "declared-terminal obligation rejection lost exact identity"
    other -> Left ("live residual obligation did not block terminal fact: " <> show other)

fatalLiveObligationRejects :: Either String ()
fatalLiveObligationRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      obligation = ObligationId "obligation.conc008.fatal"
      fatal = FatalProcessTransition
        { fatalTransitionProcess = processA
        , fatalTransitionClass = "fatal.conc008"
        , fatalTransitionDetail = "boom"
        , fatalTransitionDisposals = []
        }
  runtime <- mapLeft show $ initializeProcessRuntimeWithObligations
    network
    (Map.fromList [(processA, emptyProtocolContext), (processB, emptyProtocolContext)])
    (Map.singleton processA (Set.singleton obligation))
  case applyFatalProcessTransition fatal runtime of
    Left (FatalTerminalOpenObligations actual obligations) ->
      assert (actual == processA && obligations == Set.singleton obligation)
        "fatal-terminal obligation rejection lost exact identity"
    other -> Left ("fatal control bypassed live residual obligation: " <> show other)

rootResidueRejects :: Either String ()
rootResidueRejects = do
  before <- baseRuntime
  let (processA, processB) = processKeys (runtimeNetwork before)
      obligation = ObligationId "obligation.conc008.root"
      openRoot = emptyRootClosure
        { rootOpenObligations = Set.singleton obligation }
  afterA <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition processA) before
  afterB <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition processB) afterA
  case classifyProcessNetwork openRoot [] afterB of
    Left (RootTerminalOpenObligations obligations) ->
      assert (obligations == Set.singleton obligation)
        "root-closure rejection lost exact residual obligation"
    other -> Left ("root residual obligation did not block closure: " <> show other)

baseRuntime :: Either String ProcessRuntimeState
baseRuntime = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
  mapLeft show $ initializeProcessRuntime network (Map.fromList
    [ (processA, emptyProtocolContext)
    , (processB, emptyProtocolContext)
    ])

baseNetwork :: Either String ProcessNetwork
baseNetwork = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  mapLeft show $ activateRootProcesses network0

terminalTransition :: ProcessKey -> DeclaredTerminalTransition
terminalTransition processKey = DeclaredTerminalTransition
  { declaredTerminalProcess = processKey
  , declaredTerminalControl = Closed doneOutcome
  , declaredTerminalDisposals = []
  }

emptyRootClosure :: RootClosureState
emptyRootClosure = RootClosureState
  { rootOpenResources = Set.empty
  , rootOpenObligations = Set.empty
  , rootPendingObservables = Set.empty
  }

ownerName, loanOwnerName, endpointName :: Name
ownerName = Name "owned.resource"
loanOwnerName = Name "loan.owner"
endpointName = Name "endpoint.live"

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
