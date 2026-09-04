{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types (Digest (..))
import Phil.Core.ConcurrencyRendezvousCertification
  ( CertifiedRendezvousActivation
  , certifyRendezvousActivation
  )
import Phil.Core.ConcurrencyTerminalCertification
  ( CertifiedTerminalRuntime
  , applyDeclaredTerminalTransitionCertified
  , certifiedTerminalRuntimeState
  , initializeCertifiedTerminalRuntime
  )
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessCausality
import Phil.Core.ProcessLifecycle
import Phil.Core.Protocol (emptyProtocolContext)
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Systems.IR
import Phil.Systems.ProcessRealization
import Phil.Systems.ProcessRealizationCertification
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "certified many-to-many execution realization accepts" certifiedManyToManyAccepts
    , test "worker identity cannot substitute for certified ProcessKey" workerIdentityNativePrecedence
    , test "dropped source causality preserves native diagnostic" droppedCausalityNativePrecedence
    , test "restricted-owner drift preserves native diagnostic" ownerDriftNativePrecedence
    , test "terminal drift from certified runtime preserves native diagnostic" terminalDriftNativePrecedence
    , test "missing execution cost preserves native diagnostic" missingCostNativePrecedence
    , test "missing explicit trace preserves native diagnostic" missingTraceNativePrecedence
    , test "process/decision kernel disagreement fails closed" processKernelDisagreementRejects
    , test "event/causality kernel disagreement fails closed" eventKernelDisagreementRejects
    , test "semantic-preservation kernel disagreement fails closed" semanticKernelDisagreementRejects
    , test "trace kernel disagreement fails closed" traceKernelDisagreementRejects
    , test "outer execution-realization kernel disagreement fails closed" outerKernelDisagreementRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

certifiedManyToManyAccepts :: Either String ()
certifiedManyToManyAccepts = do
  world <- baseWorld
  certified <- mapLeft show $ verifyWorld world (worldRealization world) (worldLedger world)
  let mapping = realizationProcessExecutions (certifiedProcessExecutionRealization certified)
      (processA, processB) = worldProcesses world
  assert
    (Map.lookup processA mapping == Just (Set.fromList [sharedWorker, acceleratorStage]))
    "certified process A did not retain split physical execution"
  assert
    (Map.lookup processB mapping == Just (Set.singleton sharedWorker))
    "certified process B did not retain shared worker"

workerIdentityNativePrecedence :: Either String ()
workerIdentityNativePrecedence = do
  world <- baseWorld
  let realization0 = worldRealization world
      (_, processB) = worldProcesses world
      fakeProcess = ProcessKey (unPhysicalExecutionKey sharedWorker)
      mapping0 = realizationProcessExecutions realization0
      bad = realization0
        { realizationProcessExecutions =
            Map.insert fakeProcess (Set.singleton sharedWorker) (Map.delete processB mapping0)
        }
  case verifyWorld world bad (worldLedger world) of
    Left (ProcessExecutionRealizationNativeError (RealizationProcessSetMismatch _ _)) -> Right ()
    other -> Left ("source ProcessKey drift did not preserve native diagnostic: " <> show other)

droppedCausalityNativePrecedence :: Either String ()
droppedCausalityNativePrecedence = do
  world <- baseWorld
  let realization0 = worldRealization world
      edges0 = realizationPhysicalCausality realization0
      bad = realization0 { realizationPhysicalCausality = Set.delete (Set.findMin edges0) edges0 }
  case verifyWorld world bad (worldLedger world) of
    Left (ProcessExecutionRealizationNativeError (RealizationSourceCausalityMissing _)) -> Right ()
    other -> Left ("dropped source causality did not preserve native diagnostic: " <> show other)

ownerDriftNativePrecedence :: Either String ()
ownerDriftNativePrecedence = do
  world <- baseWorld
  let realization0 = worldRealization world
      (processA, _) = worldProcesses world
      bad = realization0
        { realizationRestrictedOwners =
            Map.singleton (ActivationOccurrenceKey "forged.owner") processA
        }
  case verifyWorld world bad (worldLedger world) of
    Left (ProcessExecutionRealizationNativeError (RealizationRestrictedOwnerMismatch expected actual)) ->
      assert (Map.null expected && not (Map.null actual))
        "restricted-owner rejection lost exact source/target distinction"
    other -> Left ("restricted-owner drift did not preserve native diagnostic: " <> show other)

terminalDriftNativePrecedence :: Either String ()
terminalDriftNativePrecedence = do
  world <- baseWorld
  let realization0 = worldRealization world
      (_, processB) = worldProcesses world
      bad = realization0
        { realizationTerminalFacts = Map.delete processB (realizationTerminalFacts realization0) }
  case verifyWorld world bad (worldLedger world) of
    Left (ProcessExecutionRealizationNativeError (RealizationTerminalFactMismatch _ _)) -> Right ()
    other -> Left ("terminal drift did not preserve native diagnostic: " <> show other)

missingCostNativePrecedence :: Either String ()
missingCostNativePrecedence = do
  world <- baseWorld
  let ledger0 = worldLedger world
      decisionId = DecisionId "exec.accelerator"
      decisions0 = loweringLedgerDecisions ledger0
      decision0 = decisions0 Map.! decisionId
      badLedger = ledger0
        { loweringLedgerDecisions =
            Map.insert decisionId (decision0 { loweringCostClass = Nothing }) decisions0
        }
  case verifyWorld world (worldRealization world) badLedger of
    Left (ProcessExecutionRealizationNativeError
      (RealizationExecutionDecisionMissingCost actualExecution actualDecision)) ->
        assert (actualExecution == acceleratorStage && actualDecision == decisionId)
          "missing-cost rejection lost execution/decision identity"
    other -> Left ("missing execution cost did not preserve native diagnostic: " <> show other)

missingTraceNativePrecedence :: Either String ()
missingTraceNativePrecedence = do
  world <- baseWorld
  let contract0 = worldStageContract world
      traces0 = stageTraceRelation contract0
      badContract = contract0 { stageTraceRelation = drop 1 traces0 }
  case certifyProcessExecutionRealization
      (worldActivation world)
      (worldRuntime world)
      (worldOrder world)
      (worldFacts world)
      badContract
      (worldLedger world)
      (worldRealization world) of
    Left (ProcessExecutionRealizationNativeError (RealizationMissingTraceRelation _)) -> Right ()
    other -> Left ("missing trace did not preserve native diagnostic: " <> show other)

processKernelDisagreementRejects :: Either String ()
processKernelDisagreementRejects =
  case verifyProcessDecisionRealizationKernelFacts
      (ProcessDecisionRealizationKernelFacts True True True False True) of
    Left (ProcessDecisionRealizationKernelDisagreement facts) ->
      assert (not (realizationDecisionCostExplicit facts))
        "process/decision kernel disagreement lost cost fact"
    other -> Left ("process/decision disagreement did not fail closed: " <> show other)

eventKernelDisagreementRejects :: Either String ()
eventKernelDisagreementRejects =
  case verifyEventCausalityRealizationKernelFacts
      (EventCausalityRealizationKernelFacts True True False True) of
    Left (EventCausalityRealizationKernelDisagreement facts) ->
      assert (not (realizationPhysicalEventInjective facts))
        "event/causality kernel disagreement lost injectivity fact"
    other -> Left ("event/causality disagreement did not fail closed: " <> show other)

semanticKernelDisagreementRejects :: Either String ()
semanticKernelDisagreementRejects =
  case verifySemanticPreservationRealizationKernelFacts
      (SemanticPreservationRealizationKernelFacts True True True False True) of
    Left (SemanticPreservationRealizationKernelDisagreement facts) ->
      assert (not (realizationTerminalFactsExact facts))
        "semantic kernel disagreement lost terminal fact"
    other -> Left ("semantic disagreement did not fail closed: " <> show other)

traceKernelDisagreementRejects :: Either String ()
traceKernelDisagreementRejects =
  case verifyTraceRealizationKernelFacts
      (TraceRealizationKernelFacts True False True) of
    Left (TraceRealizationKernelDisagreement facts) ->
      assert (not (realizationEventTraceExplicit facts))
        "trace kernel disagreement lost event-trace fact"
    other -> Left ("trace disagreement did not fail closed: " <> show other)

outerKernelDisagreementRejects :: Either String ()
outerKernelDisagreementRejects =
  case verifyProcessExecutionRealizationKernelFacts True True True False of
    Left (ProcessExecutionRealizationKernelDisagreement True True True False) -> Right ()
    other -> Left ("outer execution-realization disagreement did not fail closed: " <> show other)

data World = World
  { worldActivation :: CertifiedRendezvousActivation
  , worldRuntime :: CertifiedTerminalRuntime
  , worldOrder :: ProcessPartialOrder
  , worldFacts :: Set.Set ProcessSemanticFact
  , worldStageContract :: StageContract
  , worldLedger :: LoweringLedger
  , worldRealization :: ProcessExecutionRealization
  , worldProcesses :: (ProcessKey, ProcessKey)
  }

verifyWorld
  :: World
  -> ProcessExecutionRealization
  -> LoweringLedger
  -> Either ProcessExecutionRealizationCertificationError CertifiedProcessExecutionRealization
verifyWorld world realization ledger =
  certifyProcessExecutionRealization
    (worldActivation world)
    (worldRuntime world)
    (worldOrder world)
    (worldFacts world)
    (worldStageContract world)
    ledger
    realization

baseWorld :: Either String World
baseWorld = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  let processPair@(processA, processB) = processKeys network0
      contracts =
        [ ProcessActivationContract processA []
        , ProcessActivationContract processB []
        ]
  activation <- mapLeft show $
    certifyRendezvousActivation graph network0 contracts [] []
  runtime0 <- mapLeft show $ initializeCertifiedTerminalRuntime
    activation
    (Map.fromList
      [ (processA, emptyProtocolContext)
      , (processB, emptyProtocolContext)
      ])
    Map.empty
  runtimeA <- mapLeft show $ applyDeclaredTerminalTransitionCertified
    (terminalTransition processA (Closed (Outcome "done-a"))) runtime0
  runtime <- mapLeft show $ applyDeclaredTerminalTransitionCertified
    (terminalTransition processB (Closed (Outcome "done-b"))) runtimeA
  let network = runtimeNetwork (certifiedTerminalRuntimeState runtime)
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
  let facts = Set.fromList
        [ ProcessSemanticFact "process.effect.a" processA ProcessEffectFact "storage.write(store-a)"
        , ProcessSemanticFact "process.authority.b" processB ProcessAuthorityFact "cap.worker-b"
        ]
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
      terminalFacts = Map.mapMaybe terminalFact (runtimeStatuses (certifiedTerminalRuntimeState runtime))
      executionDecisions = Map.fromList
        [ (sharedWorker, DecisionId "exec.shared-worker")
        , (acceleratorStage, DecisionId "exec.accelerator")
        ]
      realization = ProcessExecutionRealization
        { realizationProcessExecutions = processMapping
        , realizationEventExecutions = eventMapping
        , realizationPhysicalCausality = physicalEdges
        , realizationRestrictedOwners = Map.empty
        , realizationSemanticFacts = facts
        , realizationTerminalFacts = terminalFacts
        , realizationExecutionDecisions = executionDecisions
        , realizationAssumptions = Set.singleton stageAssumption
        }
      trace =
        map (uncurry renderProcessExecutionTrace) (Map.toAscList processMapping)
          <> map (uncurry renderProcessEventTrace) (Map.toAscList eventMapping)
          <> map renderPhysicalCausalTrace (Set.toAscList physicalEdges)
      contract = baseStageContract facts trace
      ledger = baseLoweringLedger
  assert
    (Map.keysSet (processNetworkPopulation network) == Set.fromList [processA, processB])
    "certified terminal runtime changed exact process population"
  pure World
    { worldActivation = activation
    , worldRuntime = runtime
    , worldOrder = order
    , worldFacts = facts
    , worldStageContract = contract
    , worldLedger = ledger
    , worldRealization = realization
    , worldProcesses = processPair
    }
  where
    terminalFact status = case status of
      ProcessRunning -> Nothing
      ProcessTerminal fact -> Just fact

terminalTransition :: ProcessKey -> Control -> DeclaredTerminalTransition
terminalTransition processKey control = DeclaredTerminalTransition
  { declaredTerminalProcess = processKey
  , declaredTerminalControl = control
  , declaredTerminalDisposals = []
  }

baseStageContract :: Set.Set ProcessSemanticFact -> [Text] -> StageContract
baseStageContract facts trace = StageContract
  { stageContractId = "stage.conc009.production"
  , stageSourceArtifactDigest = Digest "source.conc009.production"
  , stageTargetArtifactDigest = Digest "target.conc009.production"
  , stageFacts =
      [ FactTransfer (processFactId fact) Nothing (FactConsumed "preserved in certified process realization")
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
  , loweringLedgerRoot = Digest "ledger.conc009.production"
  }

executionDecision :: DecisionId -> [Text] -> LoweringDecision
executionDecision decisionId assumptions = LoweringDecision
  { loweringDecisionId = decisionId
  , loweringDecisionDigest = Digest (unDecisionId decisionId <> ".digest")
  , loweringSourceArtifactDigest = Digest "source.conc009.production"
  , loweringTargetArtifactDigest = Digest "target.conc009.production"
  , loweringSourceRepresentation = "certified Phil process network"
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
  , loweringInspectionPlan = ["inspect certified process execution correspondence"]
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
