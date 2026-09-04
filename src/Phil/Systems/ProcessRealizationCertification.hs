module Phil.Systems.ProcessRealizationCertification
  ( ProcessDecisionRealizationKernelFacts (..)
  , EventCausalityRealizationKernelFacts (..)
  , SemanticPreservationRealizationKernelFacts (..)
  , TraceRealizationKernelFacts (..)
  , CertifiedProcessExecutionRealization
  , certifiedProcessExecutionRealization
  , ProcessExecutionRealizationCertificationError (..)
  , processDecisionRealizationKernelFacts
  , eventCausalityRealizationKernelFacts
  , semanticPreservationRealizationKernelFacts
  , traceRealizationKernelFacts
  , verifyProcessDecisionRealizationKernelFacts
  , verifyEventCausalityRealizationKernelFacts
  , verifySemanticPreservationRealizationKernelFacts
  , verifyTraceRealizationKernelFacts
  , verifyProcessExecutionRealizationKernelFacts
  , certifyProcessExecutionRealization
  ) where

import qualified ConcurrencyExecutionRealizationKernel as Kernel
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.ConcurrencyRendezvousCertification
  ( CertifiedRendezvousActivation
  , certifiedRendezvousActivationNetwork
  , certifiedRendezvousActivationState
  )
import Phil.Core.ConcurrencyTerminalCertification
  ( CertifiedTerminalRuntime
  , certifiedTerminalRuntimeState
  )
import Phil.Core.Process (ProcessNetwork (..))
import Phil.Core.ProcessActivation (ProcessActivationState (..))
import Phil.Core.ProcessCausality
  ( CausalEdge (..)
  , ProcessPartialOrder (..)
  )
import Phil.Core.ProcessLifecycle
  ( ProcessRuntimeState (..)
  , ProcessRuntimeStatus (..)
  )
import Phil.Systems.IR
  ( LoweringDecision (..)
  , LoweringLedger (..)
  , StageContract (..)
  , factTransferId
  )
import Phil.Systems.ProcessRealization
  ( PhysicalCausalEdge (..)
  , PhysicalEventKey (..)
  , PhysicalExecutionKey (..)
  , ProcessExecutionRealization (..)
  , ProcessRealizationError
  , ProcessSemanticFact (..)
  , renderPhysicalCausalTrace
  , renderProcessEventTrace
  , renderProcessExecutionTrace
  , verifyProcessExecutionRealization
  )

data ProcessDecisionRealizationKernelFacts = ProcessDecisionRealizationKernelFacts
  { realizationProcessCoverageExact :: Bool
  , realizationNoEmptyExecutionId :: Bool
  , realizationDecisionCoverageExact :: Bool
  , realizationDecisionCostExplicit :: Bool
  , realizationExecutionAssumptionsDeclared :: Bool
  }
  deriving (Eq, Show)

data EventCausalityRealizationKernelFacts = EventCausalityRealizationKernelFacts
  { realizationEventCoverageExact :: Bool
  , realizationNoEmptyPhysicalEventId :: Bool
  , realizationPhysicalEventInjective :: Bool
  , realizationSourceCausalityPreserved :: Bool
  }
  deriving (Eq, Show)

data SemanticPreservationRealizationKernelFacts = SemanticPreservationRealizationKernelFacts
  { realizationRestrictedOwnersExact :: Bool
  , realizationSemanticFactsExact :: Bool
  , realizationSemanticFactsDeclared :: Bool
  , realizationTerminalFactsExact :: Bool
  , realizationAssumptionsExact :: Bool
  }
  deriving (Eq, Show)

data TraceRealizationKernelFacts = TraceRealizationKernelFacts
  { realizationProcessTraceExplicit :: Bool
  , realizationEventTraceExplicit :: Bool
  , realizationPhysicalCausalityTraceExplicit :: Bool
  }
  deriving (Eq, Show)

newtype CertifiedProcessExecutionRealization = CertifiedProcessExecutionRealization
  { certifiedProcessExecutionRealization :: ProcessExecutionRealization
  }
  deriving (Eq, Show)

data ProcessExecutionRealizationCertificationError
  = ProcessExecutionRealizationNativeError ProcessRealizationError
  | ProcessDecisionRealizationKernelDisagreement ProcessDecisionRealizationKernelFacts
  | EventCausalityRealizationKernelDisagreement EventCausalityRealizationKernelFacts
  | SemanticPreservationRealizationKernelDisagreement SemanticPreservationRealizationKernelFacts
  | TraceRealizationKernelDisagreement TraceRealizationKernelFacts
  | ProcessExecutionRealizationKernelDisagreement Bool Bool Bool Bool
  deriving (Eq, Show)

processDecisionRealizationKernelFacts
  :: ProcessNetwork
  -> StageContract
  -> LoweringLedger
  -> ProcessExecutionRealization
  -> ProcessDecisionRealizationKernelFacts
processDecisionRealizationKernelFacts network contract ledger realization =
  ProcessDecisionRealizationKernelFacts
    { realizationProcessCoverageExact =
        Map.keysSet processMapping == sourceProcesses
          && all (not . Set.null) (Map.elems processMapping)
    , realizationNoEmptyExecutionId =
        all (not . Text.null . unPhysicalExecutionKey)
          (Set.toList referencedExecutions)
    , realizationDecisionCoverageExact =
        referencedExecutions == Map.keysSet executionDecisions
    , realizationDecisionCostExplicit =
        all decisionHasExactCost (Map.toList executionDecisions)
    , realizationExecutionAssumptionsDeclared =
        all decisionAssumptionsDeclared (Map.toList executionDecisions)
    }
  where
    sourceProcesses = Map.keysSet (processNetworkPopulation network)
    processMapping = realizationProcessExecutions realization
    referencedExecutions = Set.unions (Map.elems processMapping)
    executionDecisions = realizationExecutionDecisions realization
    stageAssumptionSet = Set.fromList (stageAssumptions contract)

    decisionHasExactCost (_, decisionId) =
      case Map.lookup decisionId (loweringLedgerDecisions ledger) of
        Nothing -> False
        Just decision ->
          loweringDecisionId decision == decisionId
            && case loweringCostClass decision of
              Nothing -> False
              Just _ -> True

    decisionAssumptionsDeclared (_, decisionId) =
      case Map.lookup decisionId (loweringLedgerDecisions ledger) of
        Nothing -> False
        Just decision ->
          loweringDecisionId decision == decisionId
            && all (`Set.member` stageAssumptionSet) (loweringAssumptions decision)

eventCausalityRealizationKernelFacts
  :: ProcessPartialOrder
  -> ProcessExecutionRealization
  -> EventCausalityRealizationKernelFacts
eventCausalityRealizationKernelFacts sourceOrder realization =
  EventCausalityRealizationKernelFacts
    { realizationEventCoverageExact =
        Map.keysSet eventMapping == Map.keysSet (partialOrderEvents sourceOrder)
    , realizationNoEmptyPhysicalEventId =
        all (not . Text.null . unPhysicalEventKey) physicalEvents
    , realizationPhysicalEventInjective =
        length physicalEvents == Set.size (Set.fromList physicalEvents)
    , realizationSourceCausalityPreserved =
        all sourceEdgePreserved (Set.toList (partialOrderEdges sourceOrder))
    }
  where
    eventMapping = realizationEventExecutions realization
    physicalEvents = Map.elems eventMapping
    physicalEdges = realizationPhysicalCausality realization

    sourceEdgePreserved edge =
      case ( Map.lookup (causalBefore edge) eventMapping
           , Map.lookup (causalAfter edge) eventMapping
           ) of
        (Just before, Just after) -> physicalPathExists physicalEdges before after
        _ -> False

semanticPreservationRealizationKernelFacts
  :: ProcessActivationState
  -> Set.Set ProcessSemanticFact
  -> ProcessRuntimeState
  -> StageContract
  -> ProcessExecutionRealization
  -> SemanticPreservationRealizationKernelFacts
semanticPreservationRealizationKernelFacts activationState sourceFacts runtime contract realization =
  SemanticPreservationRealizationKernelFacts
    { realizationRestrictedOwnersExact =
        realizationRestrictedOwners realization == expectedOwners
    , realizationSemanticFactsExact =
        realizationSemanticFacts realization == sourceFacts
    , realizationSemanticFactsDeclared =
        all (\fact -> Set.member (processFactId fact) stageFactIds)
          (Set.toList sourceFacts)
    , realizationTerminalFactsExact =
        realizationTerminalFacts realization == expectedTerminalFacts
    , realizationAssumptionsExact =
        realizationAssumptions realization == Set.fromList (stageAssumptions contract)
    }
  where
    expectedOwners = Map.map fst (activationRestrictedOwners activationState)
    stageFactIds = Set.fromList (map factTransferId (stageFacts contract))
    expectedTerminalFacts = Map.mapMaybe terminalFact (runtimeStatuses runtime)
    terminalFact status = case status of
      ProcessRunning -> Nothing
      ProcessTerminal fact -> Just fact

traceRealizationKernelFacts
  :: StageContract
  -> ProcessExecutionRealization
  -> TraceRealizationKernelFacts
traceRealizationKernelFacts contract realization =
  TraceRealizationKernelFacts
    { realizationProcessTraceExplicit = all (`Set.member` traceEntries) processEntries
    , realizationEventTraceExplicit = all (`Set.member` traceEntries) eventEntries
    , realizationPhysicalCausalityTraceExplicit =
        all (`Set.member` traceEntries) causalityEntries
    }
  where
    traceEntries = Set.fromList (stageTraceRelation contract)
    processEntries =
      map (uncurry renderProcessExecutionTrace)
        (Map.toAscList (realizationProcessExecutions realization))
    eventEntries =
      map (uncurry renderProcessEventTrace)
        (Map.toAscList (realizationEventExecutions realization))
    causalityEntries =
      map renderPhysicalCausalTrace
        (Set.toAscList (realizationPhysicalCausality realization))

verifyProcessDecisionRealizationKernelFacts
  :: ProcessDecisionRealizationKernelFacts
  -> Either ProcessExecutionRealizationCertificationError ()
verifyProcessDecisionRealizationKernelFacts facts
  | processDecisionAccepted facts = Right ()
  | otherwise = Left (ProcessDecisionRealizationKernelDisagreement facts)

verifyEventCausalityRealizationKernelFacts
  :: EventCausalityRealizationKernelFacts
  -> Either ProcessExecutionRealizationCertificationError ()
verifyEventCausalityRealizationKernelFacts facts
  | eventCausalityAccepted facts = Right ()
  | otherwise = Left (EventCausalityRealizationKernelDisagreement facts)

verifySemanticPreservationRealizationKernelFacts
  :: SemanticPreservationRealizationKernelFacts
  -> Either ProcessExecutionRealizationCertificationError ()
verifySemanticPreservationRealizationKernelFacts facts
  | semanticPreservationAccepted facts = Right ()
  | otherwise = Left (SemanticPreservationRealizationKernelDisagreement facts)

verifyTraceRealizationKernelFacts
  :: TraceRealizationKernelFacts
  -> Either ProcessExecutionRealizationCertificationError ()
verifyTraceRealizationKernelFacts facts
  | traceAccepted facts = Right ()
  | otherwise = Left (TraceRealizationKernelDisagreement facts)

verifyProcessExecutionRealizationKernelFacts
  :: Bool
  -> Bool
  -> Bool
  -> Bool
  -> Either ProcessExecutionRealizationCertificationError ()
verifyProcessExecutionRealizationKernelFacts processDecision eventCausality semanticPreservation traceExplicit
  | Kernel.decideProcessExecutionRealizationByFacts
      processDecision eventCausality semanticPreservation traceExplicit = Right ()
  | otherwise = Left
      (ProcessExecutionRealizationKernelDisagreement
        processDecision eventCausality semanticPreservation traceExplicit)

certifyProcessExecutionRealization
  :: CertifiedRendezvousActivation
  -> CertifiedTerminalRuntime
  -> ProcessPartialOrder
  -> Set.Set ProcessSemanticFact
  -> StageContract
  -> LoweringLedger
  -> ProcessExecutionRealization
  -> Either ProcessExecutionRealizationCertificationError CertifiedProcessExecutionRealization
certifyProcessExecutionRealization activation terminalRuntime sourceOrder sourceFacts contract ledger realization = do
  let network = certifiedRendezvousActivationNetwork activation
      activationState = certifiedRendezvousActivationState activation
      runtime = certifiedTerminalRuntimeState terminalRuntime
      restrictedOwners = activationRestrictedOwners activationState
  mapLeft ProcessExecutionRealizationNativeError $
    verifyProcessExecutionRealization
      network sourceOrder restrictedOwners sourceFacts runtime contract ledger realization
  let processFacts = processDecisionRealizationKernelFacts network contract ledger realization
      eventFacts = eventCausalityRealizationKernelFacts sourceOrder realization
      semanticFacts = semanticPreservationRealizationKernelFacts
        activationState sourceFacts runtime contract realization
      traceFacts = traceRealizationKernelFacts contract realization
      processAccepted = processDecisionAccepted processFacts
      eventAccepted = eventCausalityAccepted eventFacts
      semanticAccepted = semanticPreservationAccepted semanticFacts
      traceExplicit = traceAccepted traceFacts
  verifyProcessDecisionRealizationKernelFacts processFacts
  verifyEventCausalityRealizationKernelFacts eventFacts
  verifySemanticPreservationRealizationKernelFacts semanticFacts
  verifyTraceRealizationKernelFacts traceFacts
  verifyProcessExecutionRealizationKernelFacts
    processAccepted eventAccepted semanticAccepted traceExplicit
  pure (CertifiedProcessExecutionRealization realization)

processDecisionAccepted :: ProcessDecisionRealizationKernelFacts -> Bool
processDecisionAccepted facts =
  Kernel.decideProcessDecisionRealizationByFacts
    (realizationProcessCoverageExact facts)
    (realizationNoEmptyExecutionId facts)
    (realizationDecisionCoverageExact facts)
    (realizationDecisionCostExplicit facts)
    (realizationExecutionAssumptionsDeclared facts)

eventCausalityAccepted :: EventCausalityRealizationKernelFacts -> Bool
eventCausalityAccepted facts =
  Kernel.decideEventCausalityRealizationByFacts
    (realizationEventCoverageExact facts)
    (realizationNoEmptyPhysicalEventId facts)
    (realizationPhysicalEventInjective facts)
    (realizationSourceCausalityPreserved facts)

semanticPreservationAccepted :: SemanticPreservationRealizationKernelFacts -> Bool
semanticPreservationAccepted facts =
  Kernel.decideSemanticPreservationRealizationByFacts
    (realizationRestrictedOwnersExact facts)
    (realizationSemanticFactsExact facts)
    (realizationSemanticFactsDeclared facts)
    (realizationTerminalFactsExact facts)
    (realizationAssumptionsExact facts)

traceAccepted :: TraceRealizationKernelFacts -> Bool
traceAccepted facts =
  Kernel.decideTraceRealizationByFacts
    (realizationProcessTraceExplicit facts)
    (realizationEventTraceExplicit facts)
    (realizationPhysicalCausalityTraceExplicit facts)

physicalPathExists
  :: Set.Set PhysicalCausalEdge
  -> PhysicalEventKey
  -> PhysicalEventKey
  -> Bool
physicalPathExists edges start target
  | start == target = True
  | otherwise = go Set.empty [start]
  where
    adjacency = Map.fromListWith Set.union
      [ (physicalCausalBefore edge, Set.singleton (physicalCausalAfter edge))
      | edge <- Set.toList edges
      ]

    go _ [] = False
    go seen (current : rest)
      | Set.member current seen = go seen rest
      | otherwise =
          let next = Set.toList (Map.findWithDefault Set.empty current adjacency)
          in target `elem` next
              || go (Set.insert current seen) (next <> rest)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
