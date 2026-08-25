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
data SourceCallableLoweringFacts = SourceCallableLoweringFacts
  { sourceCallableContractRevision :: InterfaceRevision
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
  deriving (Eq, Ord, Show)

-- | Verify CALL-016 at the StageContract boundary. Representation choice and
-- representation identity are intentionally unconstrained; all source semantic
-- facts must remain exact in this first Phase 1 relation, while every
-- target-introduced realization consequence must be explicitly accounted.
checkCallableLoweringCorrespondence
  :: SourceCallableLoweringFacts
  -> TargetCallableLoweringFacts
  -> CallableRealizationAccounting
  -> Either CallableLoweringError CheckedCallableLowering
checkCallableLoweringCorrespondence source target accounting
  | targetCallableContractRevision target /= sourceCallableContractRevision source =
      Left (CallableLoweringContractRevisionMismatch
        (sourceCallableContractRevision source)
        (targetCallableContractRevision target))
  | targetCallableOccurrence target /= sourceCallableOccurrence source =
      Left (CallableLoweringOccurrenceMismatch
        (sourceCallableOccurrence source)
        (targetCallableOccurrence target))
  | targetCallableStructuralMode target /= sourceCallableStructuralMode source =
      Left (CallableLoweringStructuralModeMismatch
        (sourceCallableStructuralMode source)
        (targetCallableStructuralMode target))
  | targetCallableCaptures target /= sourceCallableCaptures source =
      Left (CallableLoweringCaptureMismatch
        (sourceCallableCaptures source)
        (targetCallableCaptures target))
  | targetCallableCalleeTransition target /= sourceCallableCalleeTransition source =
      Left (CallableLoweringCalleeTransitionMismatch
        (sourceCallableCalleeTransition source)
        (targetCallableCalleeTransition target))
  | targetCallableCallerAuthority target /= sourceCallableCallerAuthority source =
      Left (CallableLoweringCallerAuthorityMismatch
        (sourceCallableCallerAuthority source)
        (targetCallableCallerAuthority target))
  | targetCallableInternalAuthority target /= sourceCallableInternalAuthority source =
      Left (CallableLoweringInternalAuthorityMismatch
        (sourceCallableInternalAuthority source)
        (targetCallableInternalAuthority target))
  | targetCallableEffectBound target /= sourceCallableEffectBound source =
      Left (CallableLoweringEffectBoundMismatch
        (sourceCallableEffectBound source)
        (targetCallableEffectBound target))
  | targetCallableFailures target /= sourceCallableFailures source =
      Left (CallableLoweringFailureMismatch
        (sourceCallableFailures source)
        (targetCallableFailures target))
  | targetCallableLiveLoans target /= sourceCallableLiveLoans source =
      Left (CallableLoweringLoanScopeMismatch
        (sourceCallableLiveLoans source)
        (targetCallableLiveLoans target))
  | accountedCallableEffects accounting /= targetCallableIntroducedEffects target =
      Left (CallableLoweringEffectAccountingMismatch
        (targetCallableIntroducedEffects target)
        (accountedCallableEffects accounting))
  | accountedCallableFailures accounting /= targetCallableIntroducedFailures target =
      Left (CallableLoweringFailureAccountingMismatch
        (targetCallableIntroducedFailures target)
        (accountedCallableFailures accounting))
  | accountedCallableAssumptions accounting /= targetCallableIntroducedAssumptions target =
      Left (CallableLoweringAssumptionAccountingMismatch
        (targetCallableIntroducedAssumptions target)
        (accountedCallableAssumptions accounting))
  | accountedCallableCarriers accounting /= targetCallableIntroducedCarriers target =
      Left (CallableLoweringCarrierAccountingMismatch
        (targetCallableIntroducedCarriers target)
        (accountedCallableCarriers accounting))
  | accountedCallableCost accounting /= targetCallableIntroducedCost target =
      Left (CallableLoweringCostAccountingMismatch
        (targetCallableIntroducedCost target)
        (accountedCallableCost accounting))
  | otherwise = Right CheckedCallableLowering
      { checkedCallableLoweringSource = source
      , checkedCallableLoweringTarget = target
      , checkedCallableLoweringAccounting = accounting
      }
