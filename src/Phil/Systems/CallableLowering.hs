{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.CallableLowering
  ( TargetCallableRepresentation (..)
  , CallableCaptureSemantic (..)
  , SourceCallableLoweringFacts (..)
  , TargetCallableLoweringFacts (..)
  , CallableRealizationAccounting (..)
  , CheckedCallableLowering (..)
  , CallableLoweringError (..)
  , checkCallableLoweringCorrespondence
  ) where

import qualified CallableLoweringKernel as Kernel
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Callable
  ( CallableOccurrenceKey
  , CalleeTransition
  , CaptureOccurrenceKey
  , SemanticEffect
  )
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement
  , CallableFailure
  , CallableMachineShape
  )
import Phil.Core.CallableScope (LoanScopeKey)
import Phil.Core.Static (InterfaceRevision)
import Phil.Core.Syntax (Mode)
import Phil.Systems.IR (CostShape)

-- | Target representation is deliberately not source semantic identity.
-- A backend may pick any of these representations when the StageContract
-- correspondence preserves the source callable facts below.
data TargetCallableRepresentation
  = DirectCallable
  | CodePointerEnvironment
  | DefunctionalizedCallable Text
  | InlinedCallable
  | DeviceKernelCallable Text
  | RuntimeTrampolineCallable Text
  | OtherCallableRepresentation Text
  deriving (Eq, Ord, Show)

-- | Semantic facts attached to one captured source occurrence. Environment
-- slot numbers, pointer addresses, and backend field order are absent.
data CallableCaptureSemantic = CallableCaptureSemantic
  { callableCaptureSemanticMode :: Mode
  , callableCaptureSemanticSubject :: Maybe Text
  , callableCaptureSemanticAuthority :: Set.Set CallableAuthorityRequirement
  }
  deriving (Eq, Ord, Show)

-- | Source callable facts that CALL-016 requires target lowering to preserve.
-- Machine shape is an explicit semantic coordinate: it was present in the
-- certified CALL-016 model and is now carried by production as well.
data SourceCallableLoweringFacts = SourceCallableLoweringFacts
  { sourceCallableContractRevision :: InterfaceRevision
  , sourceCallableMachineShape :: CallableMachineShape
  , sourceCallableOccurrence :: Maybe CallableOccurrenceKey
  , sourceCallableStructuralMode :: Mode
  , sourceCallableCaptures
      :: Map.Map CaptureOccurrenceKey CallableCaptureSemantic
  , sourceCallableCalleeTransition :: CalleeTransition
  , sourceCallableCallerAuthority
      :: Set.Set CallableAuthorityRequirement
  , sourceCallableInternalAuthority
      :: Set.Set CallableAuthorityRequirement
  , sourceCallableEffectBound :: Set.Set SemanticEffect
  , sourceCallableFailures :: Set.Set CallableFailure
  , sourceCallableLiveLoans :: Set.Set LoanScopeKey
  }
  deriving (Eq, Ord, Show)

-- | Target-side semantic projection plus realization-specific consequences.
-- representationIdentity may hold a symbol/pointer/tag for inspection, but the
-- verifier never uses it as callable identity.
data TargetCallableLoweringFacts = TargetCallableLoweringFacts
  { targetCallableRepresentation :: TargetCallableRepresentation
  , targetCallableRepresentationIdentity :: Maybe Text
  , targetCallableContractRevision :: InterfaceRevision
  , targetCallableMachineShape :: CallableMachineShape
  , targetCallableOccurrence :: Maybe CallableOccurrenceKey
  , targetCallableStructuralMode :: Mode
  , targetCallableCaptures
      :: Map.Map CaptureOccurrenceKey CallableCaptureSemantic
  , targetCallableCalleeTransition :: CalleeTransition
  , targetCallableCallerAuthority
      :: Set.Set CallableAuthorityRequirement
  , targetCallableInternalAuthority
      :: Set.Set CallableAuthorityRequirement
  , targetCallableEffectBound :: Set.Set SemanticEffect
  , targetCallableFailures :: Set.Set CallableFailure
  , targetCallableLiveLoans :: Set.Set LoanScopeKey
  , targetCallableIntroducedEffects :: Set.Set SemanticEffect
  , targetCallableIntroducedFailures :: Set.Set CallableFailure
  , targetCallableIntroducedAssumptions :: Set.Set Text
  , targetCallableIntroducedCarriers :: Set.Set Text
  , targetCallableIntroducedCost :: CostShape
  }
  deriving (Eq, Ord, Show)

-- | Explicit StageContract-side accounting for target-introduced consequences.
-- Equality is intentional in this bounded slice: nothing target-introduced may
-- be left folklore, and the accounting record may not invent consequences that
-- are absent from the selected realization.
data CallableRealizationAccounting = CallableRealizationAccounting
  { accountedCallableEffects :: Set.Set SemanticEffect
  , accountedCallableFailures :: Set.Set CallableFailure
  , accountedCallableAssumptions :: Set.Set Text
  , accountedCallableCarriers :: Set.Set Text
  , accountedCallableCost :: CostShape
  }
  deriving (Eq, Ord, Show)

data CheckedCallableLowering = CheckedCallableLowering
  { checkedCallableLoweringSource :: SourceCallableLoweringFacts
  , checkedCallableLoweringTarget :: TargetCallableLoweringFacts
  , checkedCallableLoweringAccounting :: CallableRealizationAccounting
  }
  deriving (Eq, Ord, Show)

data CallableLoweringError
  = CallableLoweringContractRevisionMismatch
      InterfaceRevision InterfaceRevision
  | CallableLoweringMachineShapeMismatch
      CallableMachineShape CallableMachineShape
  | CallableLoweringOccurrenceMismatch
      (Maybe CallableOccurrenceKey) (Maybe CallableOccurrenceKey)
  | CallableLoweringStructuralModeMismatch Mode Mode
  | CallableLoweringCaptureMismatch
      (Map.Map CaptureOccurrenceKey CallableCaptureSemantic)
      (Map.Map CaptureOccurrenceKey CallableCaptureSemantic)
  | CallableLoweringCalleeTransitionMismatch
      CalleeTransition CalleeTransition
  | CallableLoweringCallerAuthorityMismatch
      (Set.Set CallableAuthorityRequirement)
      (Set.Set CallableAuthorityRequirement)
  | CallableLoweringInternalAuthorityMismatch
      (Set.Set CallableAuthorityRequirement)
      (Set.Set CallableAuthorityRequirement)
  | CallableLoweringEffectBoundMismatch
      (Set.Set SemanticEffect) (Set.Set SemanticEffect)
  | CallableLoweringFailureMismatch
      (Set.Set CallableFailure) (Set.Set CallableFailure)
  | CallableLoweringLoanScopeMismatch
      (Set.Set LoanScopeKey) (Set.Set LoanScopeKey)
  | CallableLoweringEffectAccountingMismatch
      (Set.Set SemanticEffect) (Set.Set SemanticEffect)
  | CallableLoweringFailureAccountingMismatch
      (Set.Set CallableFailure) (Set.Set CallableFailure)
  | CallableLoweringAssumptionAccountingMismatch
      (Set.Set Text) (Set.Set Text)
  | CallableLoweringCarrierAccountingMismatch
      (Set.Set Text) (Set.Set Text)
  | CallableLoweringCostAccountingMismatch CostShape CostShape
  | CallableLoweringRepresentationBridgeMismatch Text
  deriving (Eq, Ord, Show)

-- | Verify CALL-016 at the StageContract boundary. The Rocq-extracted kernel
-- owns the ordered acceptance decision over all sixteen exact coordinates.
-- Representation choice and representation identity are deliberately absent
-- from that projection. Haskell reconstructs diagnostics and can only fail
-- closed if a kernel decision disagrees with its concrete equality facts.
checkCallableLoweringCorrespondence
  :: SourceCallableLoweringFacts
  -> TargetCallableLoweringFacts
  -> CallableRealizationAccounting
  -> Either CallableLoweringError CheckedCallableLowering
checkCallableLoweringCorrespondence source target accounting =
  case Kernel.decideCallableLowering projection of
    Kernel.CallableLoweringAccepted
      | allCoordinatesMatch -> Right CheckedCallableLowering
          { checkedCallableLoweringSource = source
          , checkedCallableLoweringTarget = target
          , checkedCallableLoweringAccounting = accounting
          }
      | otherwise -> bridgeMismatch
          "kernel acceptance disagreed with concrete CALL-016 equality projection"
    Kernel.CallableLoweringContractRevisionMismatch
      | not contractRevisionEqual -> Left (CallableLoweringContractRevisionMismatch
          (sourceCallableContractRevision source)
          (targetCallableContractRevision target))
      | otherwise -> bridgeMismatch
          "contract-revision rejection disagreed with equality projection"
    Kernel.CallableLoweringMachineShapeMismatch
      | not machineShapeEqual -> Left (CallableLoweringMachineShapeMismatch
          (sourceCallableMachineShape source)
          (targetCallableMachineShape target))
      | otherwise -> bridgeMismatch
          "machine-shape rejection disagreed with equality projection"
    Kernel.CallableLoweringOccurrenceMismatch
      | not occurrenceEqual -> Left (CallableLoweringOccurrenceMismatch
          (sourceCallableOccurrence source)
          (targetCallableOccurrence target))
      | otherwise -> bridgeMismatch
          "occurrence rejection disagreed with equality projection"
    Kernel.CallableLoweringStructuralModeMismatch
      | not structuralModeEqual -> Left (CallableLoweringStructuralModeMismatch
          (sourceCallableStructuralMode source)
          (targetCallableStructuralMode target))
      | otherwise -> bridgeMismatch
          "structural-mode rejection disagreed with equality projection"
    Kernel.CallableLoweringCaptureMismatch
      | not capturesEqual -> Left (CallableLoweringCaptureMismatch
          (sourceCallableCaptures source)
          (targetCallableCaptures target))
      | otherwise -> bridgeMismatch
          "capture rejection disagreed with equality projection"
    Kernel.CallableLoweringCalleeTransitionMismatch
      | not calleeTransitionEqual -> Left (CallableLoweringCalleeTransitionMismatch
          (sourceCallableCalleeTransition source)
          (targetCallableCalleeTransition target))
      | otherwise -> bridgeMismatch
          "callee-transition rejection disagreed with equality projection"
    Kernel.CallableLoweringCallerAuthorityMismatch
      | not callerAuthorityEqual -> Left (CallableLoweringCallerAuthorityMismatch
          (sourceCallableCallerAuthority source)
          (targetCallableCallerAuthority target))
      | otherwise -> bridgeMismatch
          "caller-authority rejection disagreed with equality projection"
    Kernel.CallableLoweringInternalAuthorityMismatch
      | not internalAuthorityEqual -> Left (CallableLoweringInternalAuthorityMismatch
          (sourceCallableInternalAuthority source)
          (targetCallableInternalAuthority target))
      | otherwise -> bridgeMismatch
          "internal-authority rejection disagreed with equality projection"
    Kernel.CallableLoweringEffectBoundMismatch
      | not effectBoundEqual -> Left (CallableLoweringEffectBoundMismatch
          (sourceCallableEffectBound source)
          (targetCallableEffectBound target))
      | otherwise -> bridgeMismatch
          "effect-bound rejection disagreed with equality projection"
    Kernel.CallableLoweringFailureMismatch
      | not failuresEqual -> Left (CallableLoweringFailureMismatch
          (sourceCallableFailures source)
          (targetCallableFailures target))
      | otherwise -> bridgeMismatch
          "failure-surface rejection disagreed with equality projection"
    Kernel.CallableLoweringLoanScopeMismatch
      | not loanScopesEqual -> Left (CallableLoweringLoanScopeMismatch
          (sourceCallableLiveLoans source)
          (targetCallableLiveLoans target))
      | otherwise -> bridgeMismatch
          "loan-scope rejection disagreed with equality projection"
    Kernel.CallableLoweringEffectAccountingMismatch
      | not effectAccountingEqual -> Left (CallableLoweringEffectAccountingMismatch
          (targetCallableIntroducedEffects target)
          (accountedCallableEffects accounting))
      | otherwise -> bridgeMismatch
          "effect-accounting rejection disagreed with equality projection"
    Kernel.CallableLoweringFailureAccountingMismatch
      | not failureAccountingEqual -> Left (CallableLoweringFailureAccountingMismatch
          (targetCallableIntroducedFailures target)
          (accountedCallableFailures accounting))
      | otherwise -> bridgeMismatch
          "failure-accounting rejection disagreed with equality projection"
    Kernel.CallableLoweringAssumptionAccountingMismatch
      | not assumptionAccountingEqual -> Left (CallableLoweringAssumptionAccountingMismatch
          (targetCallableIntroducedAssumptions target)
          (accountedCallableAssumptions accounting))
      | otherwise -> bridgeMismatch
          "assumption-accounting rejection disagreed with equality projection"
    Kernel.CallableLoweringCarrierAccountingMismatch
      | not carrierAccountingEqual -> Left (CallableLoweringCarrierAccountingMismatch
          (targetCallableIntroducedCarriers target)
          (accountedCallableCarriers accounting))
      | otherwise -> bridgeMismatch
          "carrier-accounting rejection disagreed with equality projection"
    Kernel.CallableLoweringCostAccountingMismatch
      | not costAccountingEqual -> Left (CallableLoweringCostAccountingMismatch
          (targetCallableIntroducedCost target)
          (accountedCallableCost accounting))
      | otherwise -> bridgeMismatch
          "cost-accounting rejection disagreed with equality projection"
  where
    contractRevisionEqual =
      targetCallableContractRevision target == sourceCallableContractRevision source
    machineShapeEqual =
      targetCallableMachineShape target == sourceCallableMachineShape source
    occurrenceEqual =
      targetCallableOccurrence target == sourceCallableOccurrence source
    structuralModeEqual =
      targetCallableStructuralMode target == sourceCallableStructuralMode source
    capturesEqual =
      targetCallableCaptures target == sourceCallableCaptures source
    calleeTransitionEqual =
      targetCallableCalleeTransition target == sourceCallableCalleeTransition source
    callerAuthorityEqual =
      targetCallableCallerAuthority target == sourceCallableCallerAuthority source
    internalAuthorityEqual =
      targetCallableInternalAuthority target == sourceCallableInternalAuthority source
    effectBoundEqual =
      targetCallableEffectBound target == sourceCallableEffectBound source
    failuresEqual =
      targetCallableFailures target == sourceCallableFailures source
    loanScopesEqual =
      targetCallableLiveLoans target == sourceCallableLiveLoans source
    effectAccountingEqual =
      accountedCallableEffects accounting == targetCallableIntroducedEffects target
    failureAccountingEqual =
      accountedCallableFailures accounting == targetCallableIntroducedFailures target
    assumptionAccountingEqual =
      accountedCallableAssumptions accounting == targetCallableIntroducedAssumptions target
    carrierAccountingEqual =
      accountedCallableCarriers accounting == targetCallableIntroducedCarriers target
    costAccountingEqual =
      accountedCallableCost accounting == targetCallableIntroducedCost target
    projection = Kernel.MkCallableLoweringProjection
      contractRevisionEqual
      machineShapeEqual
      occurrenceEqual
      structuralModeEqual
      capturesEqual
      calleeTransitionEqual
      callerAuthorityEqual
      internalAuthorityEqual
      effectBoundEqual
      failuresEqual
      loanScopesEqual
      effectAccountingEqual
      failureAccountingEqual
      assumptionAccountingEqual
      carrierAccountingEqual
      costAccountingEqual
    allCoordinatesMatch = and
      [ contractRevisionEqual
      , machineShapeEqual
      , occurrenceEqual
      , structuralModeEqual
      , capturesEqual
      , calleeTransitionEqual
      , callerAuthorityEqual
      , internalAuthorityEqual
      , effectBoundEqual
      , failuresEqual
      , loanScopesEqual
      , effectAccountingEqual
      , failureAccountingEqual
      , assumptionAccountingEqual
      , carrierAccountingEqual
      , costAccountingEqual
      ]

bridgeMismatch :: Text -> Either CallableLoweringError a
bridgeMismatch = Left . CallableLoweringRepresentationBridgeMismatch
