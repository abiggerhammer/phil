{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types (Digest (..))
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessCausality
import Phil.Core.ProcessLifecycle
import Phil.Core.Protocol (emptyProtocolContext)
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Systems.IR
import Phil.Systems.ProcessRealization
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-009 many-to-many execution mapping preserves source semantics" manyToManyAccepted
    , test "CONC-009 worker identity cannot substitute for ProcessKey" workerIdentityCannotSubstitute
    , test "CONC-009 dropped source causality rejects" droppedCausalityRejects
    , test "CONC-009 restricted owner drift rejects" ownerDriftRejects
    , test "CONC-009 effect authority failure drift rejects" semanticFactDriftRejects
    , test "CONC-009 one worker completion cannot stand for root terminal facts" terminalDriftRejects
    , test "CONC-009 physical execution requires explicit cost decision" missingCostRejects
    , test "CONC-009 lowering assumption must remain explicit in StageContract" undeclaredAssumptionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

manyToManyAccepted :: Either String ()
manyToManyAccepted = do
  world <- baseWorld
  mapLeft show $ verifyWorld world (worldRealization world) (worldLedger world)
  let mapping = realizationProcessExecutions (worldRealization world)
      (processA, processB) = worldProcesses world
  assert
    (Map.lookup processA mapping == Just (Set.fromList [sharedWorker, acceleratorStage]))
    "process A was not split across the intended two physical execution units"
  assert
    (Map.lookup processB mapping == Just (Set.singleton sharedWorker))
    "process B did not share the intended event-loop worker"

workerIdentityCannotSubstitute :: Either String ()
workerIdentityCannotSubstitute = do
  world <- baseWorld
  let realization0 = worldRealization world
      (_, processB) = worldProcesses world
      fakeProcess = ProcessKey (unPhysicalExecutionKey sharedWorker)
      mapping0 = realizationProcessExecutions realization0
      mapping1 = Map.insert fakeProcess (Set.singleton sharedWorker) (Map.delete processB mapping0)
      bad = realization0 { realizationProcessExecutions = mapping1 }
  case verifyWorld world bad (worldLedger world) of
    Left (RealizationProcessSetMismatch _ _) -> Right ()
    other -> Left ("target worker identity was accepted as source ProcessKey: " <> show other)

droppedCausalityRejects :: Either String ()
droppedCausalityRejects = do
  world <- baseWorld
  let realization0 = worldRealization world
      edges0 = realizationPhysicalCausality realization0
      firstEdge = Set.findMin edges0
      bad = realization0 { realizationPhysicalCausality = Set.delete firstEdge edges0 }
  case verifyWorld world bad (worldLedger world) of
    Left (RealizationSourceCausalityMissing _) -> Right ()
    other -> Left ("dropped source causality was accepted: " <> show other)

ownerDriftRejects :: Either String ()
ownerDriftRejects = do
  world <- baseWorld
  let realization0 = worldRealization world
      (processA, processB) = worldProcesses world
      owners0 = realizationRestrictedOwners realization0
      owners1 = Map.map (\owner -> if owner == processA then processB else owner) owners0
      bad = realization0 { realizationRestrictedOwners = owners1 }
  case verifyWorld world bad (worldLedger world) of
    Left (RealizationRestrictedOwnerMismatch _ _) -> Right ()
    other -> Left ("restricted semantic owner drift was accepted: " <> show other)

semanticFactDriftRejects :: Either String ()
semanticFactDriftRejects = do
  world <- baseWorld
  let realization0 = worldRealization world
      facts0 = realizationSemanticFacts realization0
      victim = Set.findMin facts0
      altered = victim { processFactPayload = processFactPayload victim <> ".widened" }
      bad = realization0
        { realizationSemanticFacts = Set.insert altered (Set.delete victim facts0) }
  case verifyWorld world bad (worldLedger world) of
    Left (RealizationSemanticFactMismatch _ _) -> Right ()
    other -> Left ("process-scoped effect/authority/failure drift was accepted: " <> show other)

terminalDriftRejects :: Either String ()
terminalDriftRejects = do
  world <- baseWorld
  let realization0 = worldRealization world
      (_, processB) = worldProcesses world
      bad = realization0
        { realizationTerminalFacts = Map.delete processB (realizationTerminalFacts realization0) }
  case verifyWorld world bad (worldLedger world) of
    Left (RealizationTerminalFactMismatch _ _) -> Right ()
    other -> Left ("single-worker completion was accepted as root terminal closure: " <> show other)

missingCostRejects :: Either String ()
missingCostRejects = do
  world <- baseWorld
  let ledger0 = worldLedger world
      decisions0 = loweringLedgerDecisions ledger0
      decisionId = DecisionId "exec.accelerator"
      decision0 = decisions0 Map.! decisionId
      decision1 = decision0 { loweringCostClass = Nothing }
      badLedger = ledger0 { loweringLedgerDecisions = Map.insert decisionId decision1 decisions0 }
  case verifyWorld world (worldRealization world) badLedger of
    Left (RealizationExecutionDecisionMissingCost actualExecution actualDecision) ->
      assert
        (actualExecution == acceleratorStage && actualDecision == decisionId)
        "missing-cost rejection lost exact execution/decision identity"
    other -> Left ("physical execution without explicit cost classification was accepted: " <> show other)

undeclaredAssumptionRejects :: Either String ()
undeclaredAssumptionRejects = do
  world <- baseWorld
  let ledger0 = worldLedger world
      decisions0 = loweringLedgerDecisions ledger0
      decisionId = DecisionId "exec.shared-worker"
      decision0 = decisions0 Map.! decisionId
      decision1 = decision0 { loweringAssumptions = ["scheduler.requires.hidden-lock"] }
      badLedger = ledger0 { loweringLedgerDecisions = Map.insert decisionId decision1 decisions0 }
  case verifyWorld world (worldRealization world) badLedger of
    Left (RealizationExecutionAssumptionUndeclared actualExecution actualDecision assumption) ->
      assert
        ( actualExecution == sharedWorker
          && actualDecision == decisionId
          && assumption == "scheduler.requires.hidden-lock"
        )
        "undeclared-assumption rejection lost exact execution/decision/assumption identity"
    other -> Left ("hidden physical execution assumption was accepted: " <> show other)

data World = World
  { worldNetwork :: ProcessNetwork
  , worldOrder :: ProcessPartialOrder
  , worldRestrictedOwners :: RestrictedOwnerIndex
  , worldFacts :: Set.Set ProcessSemanticFact
  , worldRuntime :: ProcessRuntimeState
  , worldStageContract :: StageContract
  , worldLedger :: LoweringLedger
  , worldRealization :: ProcessExecutionRealization
  , worldProcesses :: (ProcessKey, ProcessKey)
  }

verifyWorld
  :: World
  -> ProcessExecutionRealization
  -> LoweringLedger
  -> Either ProcessRealizationError ()
verifyWorld world realization ledger =
  verifyProcessExecutionRealization
    (worldNetwork world)
    (worldOrder world)
    (worldRestrictedOwners world)
    (worldFacts world)
    (worldRuntime world)
    (worldStageContract world)
    ledger
    realization

baseWorld :: Either String World
baseWorld = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  network <- mapLeft show $ activateRootProcesses network0
  let processPair@(processA, processB) = processKeys network
      events =
        [ ProcessEvent eventAStart (LocalProcessEvent processA)
        , ProcessEvent eventBStart (LocalProcessEvent processB)
        , ProcessEvent eventSync (SynchronousRendezvousEvent processA processB)
        , ProcessEvent eventAEnd (LocalProcessEvent processA)
        , ProcessEvent eventBEnd (LocalProcessEvent processB)
        ]
      sequences =
        [ (processA, [eventAStart, eventSync, eventAEnd])
        , (processB, [eventBStart, eventSync, eventBEnd])
        ]
  order <- mapLeft show $ buildProcessPartialOrder events sequences []
  let owners = Map.fromList
        [ (ownerA, (processA, Name "owner.a"))
        , (ownerB, (processB, Name "owner.b"))
        ]
      facts = Set.fromList
        [ ProcessSemanticFact "process.effect.a" processA ProcessEffectFact "storage.write(store-a)"
        , ProcessSemanticFact "process.authority.a" processA ProcessAuthorityFact "cap.store-a"
        , ProcessSemanticFact "process.failure.b" processB ProcessFailureFact "io.closed"
        ]
      terminalA = ProcessTerminalFact processA (Closed (Outcome "done-a"))
      terminalB = ProcessTerminalFact processB (Closed (Outcome "done-b"))
      runtime = ProcessRuntimeState
        { runtimeNetwork = network
        , runtimeProtocolContexts = Map.fromList
            [ (processA, emptyProtocolContext)
            , (processB, emptyProtocolContext)
            ]
        , runtimeStatuses = Map.fromList
            [ (processA, ProcessTerminal terminalA)
            , (processB, ProcessTerminal terminalB)
            ]
        , runtimeOpenObligations = Map.fromList
            [ (processA, Set.empty)
            , (processB, Set.empty)
            ]
        }
      processMapping = Map.fromList
        [ (processA, Set.fromList [sharedWorker, acceleratorStage])
        , (processB, Set.singleton sharedWorker)
        ]
      eventMapping = Map.fromList
        [ (eventAStart, physicalAStart)
        , (eventBStart, physicalBStart)
        , (eventSync, physicalSync)
        , (eventAEnd, physicalAEnd)
        , (eventBEnd, physicalBEnd)
        ]
      physicalEdges = Set.fromList
        [ PhysicalCausalEdge (eventMapping Map.! causalBefore edge) (eventMapping Map.! causalAfter edge)
        | edge <- Set.toList (partialOrderEdges order)
        ]
      targetOwners = Map.map fst owners
      targetTerminals = Map.fromList [(processA, terminalA), (processB, terminalB)]
      executionDecisions = Map.fromList
        [ (sharedWorker, DecisionId "exec.shared-worker")
        , (acceleratorStage, DecisionId "exec.accelerator")
        ]
      realization = ProcessExecutionRealization
        { realizationProcessExecutions = processMapping
        , realizationEventExecutions = eventMapping
        , realizationPhysicalCausality = physicalEdges
        , realizationRestrictedOwners = targetOwners
        , realizationSemanticFacts = facts
        , realizationTerminalFacts = targetTerminals
        , realizationExecutionDecisions = executionDecisions
        , realizationAssumptions = Set.singleton stageAssumption
        }
      trace =
        map (uncurry renderProcessExecutionTrace) (Map.toAscList processMapping)
          <> map (uncurry renderProcessEventTrace) (Map.toAscList eventMapping)
          <> map renderPhysicalCausalTrace (Set.toAscList physicalEdges)
      contract = baseStageContract facts trace
      ledger = baseLoweringLedger
  pure World
    { worldNetwork = network
    , worldOrder = order
    , worldRestrictedOwners = owners
    , worldFacts = facts
    , worldRuntime = runtime
    , worldStageContract = contract
    , worldLedger = ledger
    , worldRealization = realization
    , worldProcesses = processPair
    }

baseStageContract :: Set.Set ProcessSemanticFact -> [Text] -> StageContract
baseStageContract facts trace = StageContract
  { stageContractId = "stage.conc009"
  , stageSourceArtifactDigest = Digest "source.conc009"
  , stageTargetArtifactDigest = Digest "target.conc009"
  , stageFacts =
      [ FactTransfer (processFactId fact) Nothing (FactConsumed "preserved in process realization")
      | fact <- Set.toAscList facts
      ]
  , stageInvariants = Map.empty
  , stageRequiredEdges = []
  , stageDerivedObligations = []
  , stageAssumptions = [stageAssumption]
  , stageTraceRelation = trace
  , stageResourceFailureRelation = []
  }

baseLoweringLedger :: LoweringLedger
baseLoweringLedger = LoweringLedger
  { loweringLedgerDecisions = Map.fromList
      [ (DecisionId "exec.shared-worker", executionDecision (DecisionId "exec.shared-worker") [stageAssumption])
      , (DecisionId "exec.accelerator", executionDecision (DecisionId "exec.accelerator") [])
      ]
  , loweringLedgerRoot = Digest "ledger.conc009"
  }

executionDecision :: DecisionId -> [Text] -> LoweringDecision
executionDecision decisionId assumptions = LoweringDecision
  { loweringDecisionId = decisionId
  , loweringDecisionDigest = Digest (unDecisionId decisionId <> ".digest")
  , loweringSourceArtifactDigest = Digest "source.conc009"
  , loweringTargetArtifactDigest = Digest "target.conc009"
  , loweringSourceRepresentation = "Phil process network"
  , loweringTargetRepresentation = "physical execution mechanism"
  , loweringSemanticEntities = ["ProcessKey"]
  , loweringObligationRevisions = []
  , loweringAssuranceEntries = []
  , loweringAssuranceUses = []
  , loweringAction = Materialize
  , loweringRepresentationBefore = "process"
  , loweringRepresentationAfter = "execution-unit"
  , loweringInvariantsPreserved = ["process-identity", "causality", "ownership", "terminal"]
  , loweringInvariantsTransferred = []
  , loweringRuntimeResidue = []
  , loweringCostClass = Just TargetRequired
  , loweringCostShape = emptyCostShape { costSynchronization = Just "profile-accounted" }
  , loweringTargetPreconditions = []
  , loweringAssumptions = assumptions
  , loweringDerivedObligations = []
  , loweringInspectionPlan = ["inspect process execution correspondence"]
  }

stageAssumption :: Text
stageAssumption = "scheduler.capacity.shared-worker"

sharedWorker, acceleratorStage :: PhysicalExecutionKey
sharedWorker = PhysicalExecutionKey "event-loop.worker-0"
acceleratorStage = PhysicalExecutionKey "accelerator.stage-7"

physicalAStart, physicalBStart, physicalSync, physicalAEnd, physicalBEnd :: PhysicalEventKey
physicalAStart = PhysicalEventKey "phys.a.start"
physicalBStart = PhysicalEventKey "phys.b.start"
physicalSync = PhysicalEventKey "phys.sync"
physicalAEnd = PhysicalEventKey "phys.a.end"
physicalBEnd = PhysicalEventKey "phys.b.end"

eventAStart, eventBStart, eventSync, eventAEnd, eventBEnd :: ProcessEventKey
eventAStart = ProcessEventKey "source.a.start"
eventBStart = ProcessEventKey "source.b.start"
eventSync = ProcessEventKey "source.sync"
eventAEnd = ProcessEventKey "source.a.end"
eventBEnd = ProcessEventKey "source.b.end"

ownerA, ownerB :: ActivationOccurrenceKey
ownerA = ActivationOccurrenceKey "owner.a"
ownerB = ActivationOccurrenceKey "owner.b"

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
