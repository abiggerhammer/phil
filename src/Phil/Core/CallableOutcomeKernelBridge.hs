module Phil.Core.CallableOutcomeKernelBridge
  ( KernelOutcomeBucket (..)
  , KernelResidualDisposition (..)
  , CallableOutcomeClassification (..)
  , classifyCallableOutcomeFacts
  ) where

import qualified CallableOutcomeKernel as Kernel

data KernelOutcomeBucket
  = KernelOutcomePostconditionBucket
  | KernelOutcomeAssumptionBucket
  | KernelOutcomeEffectBucket
  | KernelOutcomeDischargedFactBucket
  deriving (Eq, Show)

data KernelResidualDisposition
  = KernelResidualExact
  | KernelResidualReclassified KernelOutcomeBucket
  | KernelResidualMismatch
  deriving (Eq, Show)

data CallableOutcomeClassification
  = CallableOutcomeClassSetClassification
  | CallableOutcomeStateClassification
  | CallableOutcomeCalleeTransitionClassification
  | CallableResidualObligationReclassifiedClassification KernelOutcomeBucket
  | CallableResidualObligationMismatchClassification
  | CallableOutcomePostconditionClassification
  | CallableOutcomeAssumptionClassification
  | CallableOutcomeEffectClassification
  | CallableOutcomeDischargedFactClassification
  | CallableOutcomeAcceptedClassification
  deriving (Eq, Show)

classifyCallableOutcomeFacts
  :: Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> KernelResidualDisposition
  -> CallableOutcomeClassification
classifyCallableOutcomeFacts classDomainExact stateExact transitionExact
    residualExact postconditionsExact assumptionsExact effectsExact
    dischargedFactsExact residualDisposition =
  fromExtractedDecision $ Kernel.decideCallableOutcomeByFacts
    classDomainExact
    stateExact
    transitionExact
    residualExact
    postconditionsExact
    assumptionsExact
    effectsExact
    dischargedFactsExact
    (toExtractedDisposition residualDisposition)

toExtractedDisposition
  :: KernelResidualDisposition
  -> Kernel.ResidualDisposition
toExtractedDisposition disposition = case disposition of
  KernelResidualExact -> Kernel.ResidualExact
  KernelResidualReclassified bucket ->
    Kernel.ResidualReclassified (toExtractedBucket bucket)
  KernelResidualMismatch -> Kernel.ResidualMismatch

toExtractedBucket :: KernelOutcomeBucket -> Kernel.OutcomeBucket
toExtractedBucket bucket = case bucket of
  KernelOutcomePostconditionBucket -> Kernel.OutcomePostconditionBucket
  KernelOutcomeAssumptionBucket -> Kernel.OutcomeAssumptionBucket
  KernelOutcomeEffectBucket -> Kernel.OutcomeEffectBucket
  KernelOutcomeDischargedFactBucket -> Kernel.OutcomeDischargedFactBucket

fromExtractedBucket :: Kernel.OutcomeBucket -> KernelOutcomeBucket
fromExtractedBucket bucket = case bucket of
  Kernel.OutcomePostconditionBucket -> KernelOutcomePostconditionBucket
  Kernel.OutcomeAssumptionBucket -> KernelOutcomeAssumptionBucket
  Kernel.OutcomeEffectBucket -> KernelOutcomeEffectBucket
  Kernel.OutcomeDischargedFactBucket -> KernelOutcomeDischargedFactBucket

fromExtractedDecision
  :: Kernel.CallableOutcomeDecision
  -> CallableOutcomeClassification
fromExtractedDecision decision = case decision of
  Kernel.CallableOutcomeClassSetDecision -> CallableOutcomeClassSetClassification
  Kernel.CallableOutcomeStateDecision -> CallableOutcomeStateClassification
  Kernel.CallableOutcomeCalleeTransitionDecision ->
    CallableOutcomeCalleeTransitionClassification
  Kernel.CallableResidualObligationReclassifiedDecision bucket ->
    CallableResidualObligationReclassifiedClassification
      (fromExtractedBucket bucket)
  Kernel.CallableResidualObligationMismatchDecision ->
    CallableResidualObligationMismatchClassification
  Kernel.CallableOutcomePostconditionDecision ->
    CallableOutcomePostconditionClassification
  Kernel.CallableOutcomeAssumptionDecision ->
    CallableOutcomeAssumptionClassification
  Kernel.CallableOutcomeEffectDecision -> CallableOutcomeEffectClassification
  Kernel.CallableOutcomeDischargedFactDecision ->
    CallableOutcomeDischargedFactClassification
  Kernel.CallableOutcomeAcceptedDecision -> CallableOutcomeAcceptedClassification
