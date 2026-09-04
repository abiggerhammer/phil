{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RuntimeCarrierCoverage
  ( RuntimeCarrierKey (..)
  , RuntimeCarrierProfile (..)
  , RuntimeCarrier (..)
  , RuntimeCarrierUseDisposition (..)
  , RuntimeCarrierUse (..)
  , RuntimeCarrierTransitionDisposition (..)
  , RuntimeCarrierTransition (..)
  , RuntimeCarrierCoverageError (..)
  , checkRuntimeCarrierCoverage
  ) where

import Control.Monad (forM_, unless, when)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (RevisionId)
import Phil.Core.Process (ProcessKey)
import Phil.Systems.IR (FactTransfer (..), StageContract (..))
import Phil.Systems.ProcessRealization
  ( PhysicalExecutionKey
  , ProcessExecutionRealization (..)
  , ProcessFactKind (..)
  , ProcessSemanticFact (..)
  )

newtype RuntimeCarrierKey = RuntimeCarrierKey
  { unRuntimeCarrierKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | DEP-002 is deliberately policy/profile gated.  The carrier checker does not
-- infer that a RuntimeBound disposition is legal merely because a runtime
-- mechanism exists; its caller supplies the exact assurance-profile revision
-- and whether that profile admits runtime enforcement for this closure path.
data RuntimeCarrierProfile = RuntimeCarrierProfile
  { runtimeCarrierProfileRevision :: Text
  , runtimeCarrierProfilePermitsRuntimeBound :: Bool
  }
  deriving (Eq, Ord, Show)

-- | One exact assurance carrier for one exact residual obligation owned by one
-- semantic ProcessKey.  Physical execution keys are realization identities;
-- they describe where this carrier is established/available without becoming
-- semantic process identity.
data RuntimeCarrier = RuntimeCarrier
  { runtimeCarrierKey :: RuntimeCarrierKey
  , runtimeCarrierObligation :: RevisionId
  , runtimeCarrierProcess :: ProcessKey
  , runtimeCarrierExecutions :: Set.Set PhysicalExecutionKey
  , runtimeCarrierFailureFactId :: Text
  }
  deriving (Eq, Ord, Show)

data RuntimeCarrierUseDisposition
  = RuntimeUseStaticallySafe
  | RuntimeUseCovered RuntimeCarrierKey
  | RuntimeUseExplicitBoundary Text
  deriving (Eq, Ord, Show)

-- | Every potentially violating target use is represented explicitly.  A use
-- must either be statically safe, be covered by an exact carrier, or occur at an
-- explicit boundary.  Covered uses preserve exact source-process failure
-- attribution through 'runtimeCarrierUseFailureFactId'.
data RuntimeCarrierUse = RuntimeCarrierUse
  { runtimeCarrierUseId :: Text
  , runtimeCarrierUseObligation :: RevisionId
  , runtimeCarrierUseProcess :: ProcessKey
  , runtimeCarrierUseExecution :: PhysicalExecutionKey
  , runtimeCarrierUseFailureFactId :: Maybe Text
  , runtimeCarrierUseDisposition :: RuntimeCarrierUseDisposition
  }
  deriving (Eq, Ord, Show)

data RuntimeCarrierTransitionDisposition
  = CarrierPreserved RuntimeCarrierKey
  | CarrierReplaced RuntimeCarrierKey RuntimeCarrierKey
  | CarrierDischarged RuntimeCarrierKey Text
  | CarrierValidityEnded RuntimeCarrierKey Text
  deriving (Eq, Ord, Show)

-- | An explicit process-local execution/domain transfer.  The disposition must
-- account for the RuntimeBound carrier across the transfer; target worker or
-- device identity cannot move the obligation to another ProcessKey.
data RuntimeCarrierTransition = RuntimeCarrierTransition
  { runtimeCarrierTransitionId :: Text
  , runtimeCarrierTransitionObligation :: RevisionId
  , runtimeCarrierTransitionProcess :: ProcessKey
  , runtimeCarrierTransitionFrom :: PhysicalExecutionKey
  , runtimeCarrierTransitionTo :: PhysicalExecutionKey
  , runtimeCarrierTransitionDisposition :: RuntimeCarrierTransitionDisposition
  }
  deriving (Eq, Ord, Show)

data RuntimeCarrierCoverageError
  = RuntimeCarrierProfileRevisionEmpty
  | RuntimeCarrierRuntimeBoundForbidden Text
  | RuntimeCarrierMapKeyMismatch RuntimeCarrierKey RuntimeCarrierKey
  | RuntimeCarrierObligationNotDerived RuntimeCarrierKey RevisionId
  | RuntimeCarrierUnknownProcess RuntimeCarrierKey ProcessKey
  | RuntimeCarrierEmptyExecutionSet RuntimeCarrierKey
  | RuntimeCarrierExecutionOutsideProcess RuntimeCarrierKey ProcessKey PhysicalExecutionKey
  | RuntimeCarrierFailureFactUnknown RuntimeCarrierKey Text
  | RuntimeCarrierFailureFactAmbiguous RuntimeCarrierKey Text
  | RuntimeCarrierFailureFactKindMismatch RuntimeCarrierKey Text ProcessFactKind
  | RuntimeCarrierFailureFactProcessMismatch RuntimeCarrierKey Text ProcessKey ProcessKey
  | RuntimeCarrierUseIdEmpty
  | RuntimeCarrierUseObligationNotDerived Text RevisionId
  | RuntimeCarrierUseUnknownProcess Text ProcessKey
  | RuntimeCarrierUseExecutionOutsideProcess Text ProcessKey PhysicalExecutionKey
  | RuntimeCarrierUseBoundaryEmpty Text
  | RuntimeCarrierUseUnknownCarrier Text RuntimeCarrierKey
  | RuntimeCarrierUseObligationMismatch Text RevisionId RevisionId
  | RuntimeCarrierUseProcessMismatch Text ProcessKey ProcessKey
  | RuntimeCarrierUseExecutionUncovered Text RuntimeCarrierKey PhysicalExecutionKey
  | RuntimeCarrierUseFailureFactMissing Text
  | RuntimeCarrierUseFailureFactMismatch Text Text Text
  | RuntimeCarrierTransitionIdEmpty
  | RuntimeCarrierTransitionObligationNotDerived Text RevisionId
  | RuntimeCarrierTransitionUnknownProcess Text ProcessKey
  | RuntimeCarrierTransitionExecutionOutsideProcess Text ProcessKey PhysicalExecutionKey
  | RuntimeCarrierTransitionUnknownCarrier Text RuntimeCarrierKey
  | RuntimeCarrierTransitionCarrierObligationMismatch Text RuntimeCarrierKey RevisionId RevisionId
  | RuntimeCarrierTransitionCarrierProcessMismatch Text RuntimeCarrierKey ProcessKey ProcessKey
  | RuntimeCarrierTransitionFromUncovered Text RuntimeCarrierKey PhysicalExecutionKey
  | RuntimeCarrierTransitionToUncovered Text RuntimeCarrierKey PhysicalExecutionKey
  | RuntimeCarrierTransitionReasonEmpty Text
  | RuntimeCarrierTransitionDestinationStillRuntimeBound Text Text
  deriving (Eq, Show)

checkRuntimeCarrierCoverage
  :: RuntimeCarrierProfile
  -> StageContract
  -> ProcessExecutionRealization
  -> Map.Map RuntimeCarrierKey RuntimeCarrier
  -> [RuntimeCarrierUse]
  -> [RuntimeCarrierTransition]
  -> Either RuntimeCarrierCoverageError ()
checkRuntimeCarrierCoverage profile contract realization carriers uses transitions = do
  when (Text.null (runtimeCarrierProfileRevision profile)) $
    Left RuntimeCarrierProfileRevisionEmpty
  when (runtimeBoundPresent && not (runtimeCarrierProfilePermitsRuntimeBound profile)) $
    Left (RuntimeCarrierRuntimeBoundForbidden (runtimeCarrierProfileRevision profile))
  forM_ (Map.toAscList carriers) validateCarrier
  forM_ uses validateUse
  forM_ transitions validateTransition
  where
    runtimeBoundPresent =
      not (Map.null carriers)
        || any isCoveredUse uses
        || not (null transitions)

    stageObligations = Set.fromList
      ( stageDerivedObligations contract
        <> [ revision
           | fact <- stageFacts contract
           , Just revision <- [factSourceRevision fact]
           ]
      )
    processExecutions = realizationProcessExecutions realization
    factsById = Map.fromListWith (<>)
      [ (processFactId fact, [fact])
      | fact <- Set.toAscList (realizationSemanticFacts realization)
      ]

    isCoveredUse use = case runtimeCarrierUseDisposition use of
      RuntimeUseCovered _ -> True
      _ -> False

    validateCarrier (mapKey, carrier) = do
      unless (mapKey == runtimeCarrierKey carrier) $
        Left (RuntimeCarrierMapKeyMismatch mapKey (runtimeCarrierKey carrier))
      unless (Set.member (runtimeCarrierObligation carrier) stageObligations) $
        Left (RuntimeCarrierObligationNotDerived
          mapKey (runtimeCarrierObligation carrier))
      executions <- case Map.lookup (runtimeCarrierProcess carrier) processExecutions of
        Nothing -> Left (RuntimeCarrierUnknownProcess mapKey (runtimeCarrierProcess carrier))
        Just value -> Right value
      when (Set.null (runtimeCarrierExecutions carrier)) $
        Left (RuntimeCarrierEmptyExecutionSet mapKey)
      forM_ (Set.toAscList (runtimeCarrierExecutions carrier)) $ \execution ->
        unless (Set.member execution executions) $
          Left (RuntimeCarrierExecutionOutsideProcess
            mapKey (runtimeCarrierProcess carrier) execution)
      validateFailureFact carrier

    validateFailureFact carrier =
      case Map.lookup (runtimeCarrierFailureFactId carrier) factsById of
        Nothing -> Left (RuntimeCarrierFailureFactUnknown
          (runtimeCarrierKey carrier) (runtimeCarrierFailureFactId carrier))
        Just [] -> Left (RuntimeCarrierFailureFactUnknown
          (runtimeCarrierKey carrier) (runtimeCarrierFailureFactId carrier))
        Just [fact] -> do
          unless (processFactKind fact == ProcessFailureFact) $
            Left (RuntimeCarrierFailureFactKindMismatch
              (runtimeCarrierKey carrier)
              (runtimeCarrierFailureFactId carrier)
              (processFactKind fact))
          unless (processFactProcess fact == runtimeCarrierProcess carrier) $
            Left (RuntimeCarrierFailureFactProcessMismatch
              (runtimeCarrierKey carrier)
              (runtimeCarrierFailureFactId carrier)
              (runtimeCarrierProcess carrier)
              (processFactProcess fact))
        Just _ -> Left (RuntimeCarrierFailureFactAmbiguous
          (runtimeCarrierKey carrier) (runtimeCarrierFailureFactId carrier))

    validateUse use = do
      when (Text.null (runtimeCarrierUseId use)) $
        Left RuntimeCarrierUseIdEmpty
      unless (Set.member (runtimeCarrierUseObligation use) stageObligations) $
        Left (RuntimeCarrierUseObligationNotDerived
          (runtimeCarrierUseId use) (runtimeCarrierUseObligation use))
      executions <- case Map.lookup (runtimeCarrierUseProcess use) processExecutions of
        Nothing -> Left (RuntimeCarrierUseUnknownProcess
          (runtimeCarrierUseId use) (runtimeCarrierUseProcess use))
        Just value -> Right value
      unless (Set.member (runtimeCarrierUseExecution use) executions) $
        Left (RuntimeCarrierUseExecutionOutsideProcess
          (runtimeCarrierUseId use)
          (runtimeCarrierUseProcess use)
          (runtimeCarrierUseExecution use))
      case runtimeCarrierUseDisposition use of
        RuntimeUseStaticallySafe -> Right ()
        RuntimeUseExplicitBoundary boundary ->
          when (Text.null boundary) $
            Left (RuntimeCarrierUseBoundaryEmpty (runtimeCarrierUseId use))
        RuntimeUseCovered carrierKey -> do
          carrier <- lookupUseCarrier use carrierKey
          unless (Set.member (runtimeCarrierUseExecution use) (runtimeCarrierExecutions carrier)) $
            Left (RuntimeCarrierUseExecutionUncovered
              (runtimeCarrierUseId use) carrierKey (runtimeCarrierUseExecution use))
          case runtimeCarrierUseFailureFactId use of
            Nothing -> Left (RuntimeCarrierUseFailureFactMissing (runtimeCarrierUseId use))
            Just actual -> unless (actual == runtimeCarrierFailureFactId carrier) $
              Left (RuntimeCarrierUseFailureFactMismatch
                (runtimeCarrierUseId use)
                (runtimeCarrierFailureFactId carrier)
                actual)

    lookupUseCarrier use carrierKey = do
      carrier <- case Map.lookup carrierKey carriers of
        Nothing -> Left (RuntimeCarrierUseUnknownCarrier (runtimeCarrierUseId use) carrierKey)
        Just value -> Right value
      unless (runtimeCarrierUseObligation use == runtimeCarrierObligation carrier) $
        Left (RuntimeCarrierUseObligationMismatch
          (runtimeCarrierUseId use)
          (runtimeCarrierObligation carrier)
          (runtimeCarrierUseObligation use))
      unless (runtimeCarrierUseProcess use == runtimeCarrierProcess carrier) $
        Left (RuntimeCarrierUseProcessMismatch
          (runtimeCarrierUseId use)
          (runtimeCarrierProcess carrier)
          (runtimeCarrierUseProcess use))
      Right carrier

    validateTransition transition = do
      when (Text.null (runtimeCarrierTransitionId transition)) $
        Left RuntimeCarrierTransitionIdEmpty
      unless (Set.member (runtimeCarrierTransitionObligation transition) stageObligations) $
        Left (RuntimeCarrierTransitionObligationNotDerived
          (runtimeCarrierTransitionId transition)
          (runtimeCarrierTransitionObligation transition))
      executions <- case Map.lookup (runtimeCarrierTransitionProcess transition) processExecutions of
        Nothing -> Left (RuntimeCarrierTransitionUnknownProcess
          (runtimeCarrierTransitionId transition)
          (runtimeCarrierTransitionProcess transition))
        Just value -> Right value
      forM_ [runtimeCarrierTransitionFrom transition, runtimeCarrierTransitionTo transition] $ \execution ->
        unless (Set.member execution executions) $
          Left (RuntimeCarrierTransitionExecutionOutsideProcess
            (runtimeCarrierTransitionId transition)
            (runtimeCarrierTransitionProcess transition)
            execution)
      case runtimeCarrierTransitionDisposition transition of
        CarrierPreserved carrierKey -> do
          carrier <- lookupTransitionCarrier transition carrierKey
          requireCarrierExecution transition carrierKey carrier
            (runtimeCarrierTransitionFrom transition) True
          requireCarrierExecution transition carrierKey carrier
            (runtimeCarrierTransitionTo transition) False
        CarrierReplaced priorKey nextKey -> do
          prior <- lookupTransitionCarrier transition priorKey
          next <- lookupTransitionCarrier transition nextKey
          requireCarrierExecution transition priorKey prior
            (runtimeCarrierTransitionFrom transition) True
          requireCarrierExecution transition nextKey next
            (runtimeCarrierTransitionTo transition) False
        CarrierDischarged carrierKey reason -> do
          when (Text.null reason) $
            Left (RuntimeCarrierTransitionReasonEmpty (runtimeCarrierTransitionId transition))
          carrier <- lookupTransitionCarrier transition carrierKey
          requireCarrierExecution transition carrierKey carrier
            (runtimeCarrierTransitionFrom transition) True
          ensureDestinationNotRuntimeBound transition
        CarrierValidityEnded carrierKey reason -> do
          when (Text.null reason) $
            Left (RuntimeCarrierTransitionReasonEmpty (runtimeCarrierTransitionId transition))
          carrier <- lookupTransitionCarrier transition carrierKey
          requireCarrierExecution transition carrierKey carrier
            (runtimeCarrierTransitionFrom transition) True
          ensureDestinationNotRuntimeBound transition

    lookupTransitionCarrier transition carrierKey = do
      carrier <- case Map.lookup carrierKey carriers of
        Nothing -> Left (RuntimeCarrierTransitionUnknownCarrier
          (runtimeCarrierTransitionId transition) carrierKey)
        Just value -> Right value
      unless (runtimeCarrierTransitionObligation transition == runtimeCarrierObligation carrier) $
        Left (RuntimeCarrierTransitionCarrierObligationMismatch
          (runtimeCarrierTransitionId transition)
          carrierKey
          (runtimeCarrierObligation carrier)
          (runtimeCarrierTransitionObligation transition))
      unless (runtimeCarrierTransitionProcess transition == runtimeCarrierProcess carrier) $
        Left (RuntimeCarrierTransitionCarrierProcessMismatch
          (runtimeCarrierTransitionId transition)
          carrierKey
          (runtimeCarrierProcess carrier)
          (runtimeCarrierTransitionProcess transition))
      Right carrier

    requireCarrierExecution transition carrierKey carrier execution isFrom =
      unless (Set.member execution (runtimeCarrierExecutions carrier)) $
        if isFrom
          then Left (RuntimeCarrierTransitionFromUncovered
            (runtimeCarrierTransitionId transition) carrierKey execution)
          else Left (RuntimeCarrierTransitionToUncovered
            (runtimeCarrierTransitionId transition) carrierKey execution)

    ensureDestinationNotRuntimeBound transition =
      case
        [ runtimeCarrierUseId use
        | use <- uses
        , runtimeCarrierUseProcess use == runtimeCarrierTransitionProcess transition
        , runtimeCarrierUseObligation use == runtimeCarrierTransitionObligation transition
        , runtimeCarrierUseExecution use == runtimeCarrierTransitionTo transition
        , RuntimeUseCovered _ <- [runtimeCarrierUseDisposition use]
        ] of
        [] -> Right ()
        useId : _ -> Left (RuntimeCarrierTransitionDestinationStillRuntimeBound
          (runtimeCarrierTransitionId transition) useId)
