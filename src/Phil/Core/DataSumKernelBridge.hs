module Phil.Core.DataSumKernelBridge
  ( constructorSelectionAccepted
  , selectedPayloadRestorationAccepted
  , continuingArmAccepted
  , branchConvergenceAccepted
  ) where

import qualified DataSumKernel as Kernel

constructorSelectionAccepted :: Bool -> Bool
constructorSelectionAccepted constructorDeclared =
  case Kernel.decideConstructorSelectionByFact constructorDeclared of
    Kernel.ConstructorSelectionAcceptedDecision -> True
    Kernel.ConstructorSelectionUnknownDecision -> False

selectedPayloadRestorationAccepted :: Bool -> Bool -> Bool
selectedPayloadRestorationAccepted aggregateConsumed payloadRestoredExact =
  case Kernel.decideSelectedPayloadRestorationByFacts
    aggregateConsumed payloadRestoredExact of
    Kernel.SelectedPayloadRestorationAcceptedDecision -> True
    Kernel.SelectedPayloadAggregateDecision -> False
    Kernel.SelectedPayloadExactnessDecision -> False

continuingArmAccepted :: Bool -> Bool
continuingArmAccepted selectedPayloadAccounted =
  case Kernel.decideContinuingArmByFact selectedPayloadAccounted of
    Kernel.ContinuingArmAcceptedDecision -> True
    Kernel.ContinuingArmPayloadDispositionDecision -> False

branchConvergenceAccepted :: Bool -> Bool -> Bool -> Bool
branchConvergenceAccepted
    rawLinearShapesCompatible explicitCommonPackage ordinaryJoinAccepted =
  case Kernel.decideBranchConvergenceByFacts
    rawLinearShapesCompatible explicitCommonPackage ordinaryJoinAccepted of
    Kernel.BranchConvergenceAcceptedDecision -> True
    Kernel.BranchConvergenceHiddenStateDecision -> False
    Kernel.BranchConvergenceJoinDecision -> False
