{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.ProcessRealization
  ( PhysicalExecutionKey (..)
  , PhysicalEventKey (..)
  , PhysicalCausalEdge (..)
  , ProcessFactKind (..)
  , ProcessSemanticFact (..)
  , ProcessExecutionRealization (..)
  , ProcessRealizationError (..)
  , verifyProcessExecutionRealization
  , renderProcessExecutionTrace
  , renderProcessEventTrace
  , renderPhysicalCausalTrace
  ) where

import Control.Monad (forM_, unless, when)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Process
  ( ProcessKey (..)
  , ProcessNetwork (..)
  )
import Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey
  , RestrictedOwnerIndex
  )
import Phil.Core.ProcessCausality
  ( CausalEdge (..)
  , ProcessEventKey (..)
  , ProcessPartialOrder (..)
  )
import Phil.Core.ProcessLifecycle
  ( ProcessRuntimeState (..)
  , ProcessRuntimeStatus (..)
  , ProcessTerminalFact
  )
import Phil.Systems.IR
  ( CostClass
  , DecisionId (..)
  , LoweringDecision (..)
  , LoweringLedger (..)
  , StageContract (..)
  , factTransferId
  )

newtype PhysicalExecutionKey = PhysicalExecutionKey
  { unPhysicalExecutionKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype PhysicalEventKey = PhysicalEventKey
  { unPhysicalEventKey :: Text
  }
  deriving (Eq, Ord, Show)

data PhysicalCausalEdge = PhysicalCausalEdge
  { physicalCausalBefore :: PhysicalEventKey
  , physicalCausalAfter :: PhysicalEventKey
  }
  deriving (Eq, Ord, Show)

data ProcessFactKind
  = ProcessEffectFact
  | ProcessAuthorityFact
  | ProcessFailureFact
  deriving (Eq, Ord, Show)

data ProcessSemanticFact = ProcessSemanticFact
  { processFactId :: Text
  , processFactProcess :: ProcessKey
  , processFactKind :: ProcessFactKind
  , processFactPayload :: Text
  }
  deriving (Eq, Ord, Show)

-- | A target execution realization is intentionally many-to-many.  Source
-- ProcessKey identity remains the key of the correspondence while physical
-- workers/tasks/stages are replaceable realization identities.
data ProcessExecutionRealization = ProcessExecutionRealization
  { realizationProcessExecutions :: Map.Map ProcessKey (Set PhysicalExecutionKey)
  , realizationEventExecutions :: Map.Map ProcessEventKey PhysicalEventKey
  , realizationPhysicalCausality :: Set PhysicalCausalEdge
  , realizationRestrictedOwners :: Map.Map ActivationOccurrenceKey ProcessKey
  , realizationSemanticFacts :: Set ProcessSemanticFact
  , realizationTerminalFacts :: Map.Map ProcessKey ProcessTerminalFact
  , realizationExecutionDecisions :: Map.Map PhysicalExecutionKey DecisionId
  , realizationAssumptions :: Set Text
  }
  deriving (Eq, Show)

data ProcessRealizationError
  = RealizationRuntimeNetworkMismatch
  | RealizationProcessSetMismatch (Set ProcessKey) (Set ProcessKey)
  | RealizationProcessWithoutExecution ProcessKey
  | RealizationEmptyExecutionKey ProcessKey
  | RealizationExecutionDecisionSetMismatch
      (Set PhysicalExecutionKey)
      (Set PhysicalExecutionKey)
  | RealizationUnknownExecutionDecision PhysicalExecutionKey DecisionId
  | RealizationDecisionMapKeyMismatch DecisionId DecisionId
  | RealizationExecutionDecisionMissingCost PhysicalExecutionKey DecisionId
  | RealizationExecutionAssumptionUndeclared PhysicalExecutionKey DecisionId Text
  | RealizationEventSetMismatch (Set ProcessEventKey) (Set ProcessEventKey)
  | RealizationEmptyPhysicalEventKey ProcessEventKey
  | RealizationPhysicalEventAlias PhysicalEventKey ProcessEventKey ProcessEventKey
  | RealizationSourceCausalityMissing CausalEdge
  | RealizationRestrictedOwnerMismatch
      (Map.Map ActivationOccurrenceKey ProcessKey)
      (Map.Map ActivationOccurrenceKey ProcessKey)
  | RealizationSemanticFactMismatch
      (Set ProcessSemanticFact)
      (Set ProcessSemanticFact)
  | RealizationProcessFactNotInStageContract Text
  | RealizationTerminalFactMismatch
      (Map.Map ProcessKey ProcessTerminalFact)
      (Map.Map ProcessKey ProcessTerminalFact)
  | RealizationStageAssumptionMismatch (Set Text) (Set Text)
  | RealizationMissingTraceRelation Text
  deriving (Eq, Show)

verifyProcessExecutionRealization
  :: ProcessNetwork
  -> ProcessPartialOrder
  -> RestrictedOwnerIndex
  -> Set ProcessSemanticFact
  -> ProcessRuntimeState
  -> StageContract
  -> LoweringLedger
  -> ProcessExecutionRealization
  -> Either ProcessRealizationError ()
verifyProcessExecutionRealization network sourceOrder restrictedOwners sourceFacts runtime contract ledger realization = do
  unless (runtimeNetwork runtime == network) $
    Left RealizationRuntimeNetworkMismatch
  verifyProcessMapping
  verifyExecutionDecisions
  verifyEventMapping
  verifyCausality
  verifyOwners
  verifyFacts
  verifyTerminalFacts
  verifyAssumptions
  verifyTraceRelation
  where
    sourceProcesses = Map.keysSet (processNetworkPopulation network)

    verifyProcessMapping = do
      let actualProcesses = Map.keysSet (realizationProcessExecutions realization)
      unless (actualProcesses == sourceProcesses) $
        Left (RealizationProcessSetMismatch sourceProcesses actualProcesses)
      forM_ (Map.toAscList (realizationProcessExecutions realization)) $ \(processKey, executions) -> do
        when (Set.null executions) $
          Left (RealizationProcessWithoutExecution processKey)
        when (any (Text.null . unPhysicalExecutionKey) (Set.toList executions)) $
          Left (RealizationEmptyExecutionKey processKey)

    verifyExecutionDecisions = do
      let referencedExecutions = Set.unions (Map.elems (realizationProcessExecutions realization))
          decisionExecutions = Map.keysSet (realizationExecutionDecisions realization)
      unless (referencedExecutions == decisionExecutions) $
        Left (RealizationExecutionDecisionSetMismatch referencedExecutions decisionExecutions)
      forM_ (Map.toAscList (realizationExecutionDecisions realization)) $ \(executionKey, decisionId) ->
        case Map.lookup decisionId (loweringLedgerDecisions ledger) of
          Nothing -> Left (RealizationUnknownExecutionDecision executionKey decisionId)
          Just decision -> do
            unless (loweringDecisionId decision == decisionId) $
              Left (RealizationDecisionMapKeyMismatch decisionId (loweringDecisionId decision))
            case loweringCostClass decision of
              Nothing -> Left (RealizationExecutionDecisionMissingCost executionKey decisionId)
              Just (_ :: CostClass) -> pure ()
            forM_ (loweringAssumptions decision) $ \assumption ->
              unless (Set.member assumption (Set.fromList (stageAssumptions contract))) $
                Left (RealizationExecutionAssumptionUndeclared executionKey decisionId assumption)

    verifyEventMapping = do
      let expectedEvents = Map.keysSet (partialOrderEvents sourceOrder)
          actualEvents = Map.keysSet (realizationEventExecutions realization)
      unless (expectedEvents == actualEvents) $
        Left (RealizationEventSetMismatch expectedEvents actualEvents)
      forM_ (Map.toAscList (realizationEventExecutions realization)) $ \(eventKey, physicalKey) ->
        when (Text.null (unPhysicalEventKey physicalKey)) $
          Left (RealizationEmptyPhysicalEventKey eventKey)
      ensureNoPhysicalAliases Map.empty (Map.toAscList (realizationEventExecutions realization))

    ensureNoPhysicalAliases _ [] = Right ()
    ensureNoPhysicalAliases seen ((sourceEvent, physicalEvent) : rest) =
      case Map.lookup physicalEvent seen of
        Just firstSource -> Left (RealizationPhysicalEventAlias physicalEvent firstSource sourceEvent)
        Nothing -> ensureNoPhysicalAliases (Map.insert physicalEvent sourceEvent seen) rest

    verifyCausality =
      forM_ (Set.toAscList (partialOrderEdges sourceOrder)) $ \sourceEdge -> do
        let before = realizationEventExecutions realization Map.! causalBefore sourceEdge
            after = realizationEventExecutions realization Map.! causalAfter sourceEdge
        unless (physicalPathExists (realizationPhysicalCausality realization) before after) $
          Left (RealizationSourceCausalityMissing sourceEdge)

    verifyOwners = do
      let expectedOwners = Map.map fst restrictedOwners
          actualOwners = realizationRestrictedOwners realization
      unless (expectedOwners == actualOwners) $
        Left (RealizationRestrictedOwnerMismatch expectedOwners actualOwners)

    verifyFacts = do
      let actualFacts = realizationSemanticFacts realization
      unless (actualFacts == sourceFacts) $
        Left (RealizationSemanticFactMismatch sourceFacts actualFacts)
      let stageFactIds = Set.fromList (map factTransferId (stageFacts contract))
      forM_ (Set.toAscList sourceFacts) $ \fact ->
        unless (Set.member (processFactId fact) stageFactIds) $
          Left (RealizationProcessFactNotInStageContract (processFactId fact))

    verifyTerminalFacts = do
      let expectedFacts = Map.mapMaybe terminalFact (runtimeStatuses runtime)
          actualFacts = realizationTerminalFacts realization
      unless (expectedFacts == actualFacts) $
        Left (RealizationTerminalFactMismatch expectedFacts actualFacts)

    terminalFact status = case status of
      ProcessRunning -> Nothing
      ProcessTerminal fact -> Just fact

    verifyAssumptions = do
      let expected = Set.fromList (stageAssumptions contract)
          actual = realizationAssumptions realization
      unless (expected == actual) $
        Left (RealizationStageAssumptionMismatch expected actual)

    verifyTraceRelation = do
      let traceEntries = Set.fromList (stageTraceRelation contract)
          required =
            map (uncurry renderProcessExecutionTrace) (Map.toAscList (realizationProcessExecutions realization))
              <> map (uncurry renderProcessEventTrace) (Map.toAscList (realizationEventExecutions realization))
              <> map renderPhysicalCausalTrace (Set.toAscList (realizationPhysicalCausality realization))
      forM_ required $ \entry ->
        unless (Set.member entry traceEntries) $
          Left (RealizationMissingTraceRelation entry)

physicalPathExists
  :: Set PhysicalCausalEdge
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

renderProcessExecutionTrace :: ProcessKey -> Set PhysicalExecutionKey -> Text
renderProcessExecutionTrace processKey executions =
  "process-realization:" <> unProcessKey processKey <> "=>" <>
    Text.intercalate "," (map unPhysicalExecutionKey (Set.toAscList executions))

renderProcessEventTrace :: ProcessEventKey -> PhysicalEventKey -> Text
renderProcessEventTrace sourceEvent physicalEvent =
  "process-event:" <> unProcessEventKey sourceEvent <> "=>" <> unPhysicalEventKey physicalEvent

renderPhysicalCausalTrace :: PhysicalCausalEdge -> Text
renderPhysicalCausalTrace edge =
  "physical-causality:" <> unPhysicalEventKey (physicalCausalBefore edge)
    <> "->" <> unPhysicalEventKey (physicalCausalAfter edge)
