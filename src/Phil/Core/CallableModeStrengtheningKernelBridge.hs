module Phil.Core.CallableModeStrengtheningKernelBridge
  ( ExplicitClosureModeClassification (..)
  , CheckedClosureModeShapeClassification (..)
  , classifyExplicitClosureModeFacts
  , classifyCheckedClosureModeShapeFacts
  ) where

import qualified CallableModeStrengtheningKernel as Kernel

data ExplicitClosureModeClassification
  = ExplicitClosureModeWeakeningClassification
  | ExplicitClosureModeEqualClassification
  | ExplicitClosureModeMissingJustificationClassification
  | ExplicitClosureModeTargetImplementationClassification
  | ExplicitClosureModeWrongContractClassification
  | ExplicitClosureModeEmptyJustificationClassification
  | ExplicitClosureModeStrengthenedClassification
  deriving (Eq, Show)

data CheckedClosureModeShapeClassification
  = CheckedClosureModeMinimumClassification
  | CheckedClosureModeSelectedClassification
  | CheckedClosureModeJustificationClassification
  | CheckedClosureModeShapeAcceptedClassification
  deriving (Eq, Show)

classifyExplicitClosureModeFacts
  :: Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> ExplicitClosureModeClassification
classifyExplicitClosureModeFacts nonWeakening equalToMinimum
    justificationPresent targetImplementationReason contractMatches
    detailPresent =
  case Kernel.decideExplicitClosureModeByFacts
      nonWeakening
      equalToMinimum
      justificationPresent
      targetImplementationReason
      contractMatches
      detailPresent of
    Kernel.ExplicitClosureModeWeakeningDecision ->
      ExplicitClosureModeWeakeningClassification
    Kernel.ExplicitClosureModeEqualDecision ->
      ExplicitClosureModeEqualClassification
    Kernel.ExplicitClosureModeMissingJustificationDecision ->
      ExplicitClosureModeMissingJustificationClassification
    Kernel.ExplicitClosureModeTargetImplementationDecision ->
      ExplicitClosureModeTargetImplementationClassification
    Kernel.ExplicitClosureModeWrongContractDecision ->
      ExplicitClosureModeWrongContractClassification
    Kernel.ExplicitClosureModeEmptyJustificationDecision ->
      ExplicitClosureModeEmptyJustificationClassification
    Kernel.ExplicitClosureModeStrengthenedDecision ->
      ExplicitClosureModeStrengthenedClassification

classifyCheckedClosureModeShapeFacts
  :: Bool
  -> Bool
  -> Bool
  -> CheckedClosureModeShapeClassification
classifyCheckedClosureModeShapeFacts minimumExact selectedExact justificationExact =
  case Kernel.decideCheckedClosureModeShapeByFacts
      minimumExact selectedExact justificationExact of
    Kernel.CheckedClosureModeMinimumDecision ->
      CheckedClosureModeMinimumClassification
    Kernel.CheckedClosureModeSelectedDecision ->
      CheckedClosureModeSelectedClassification
    Kernel.CheckedClosureModeJustificationDecision ->
      CheckedClosureModeJustificationClassification
    Kernel.CheckedClosureModeShapeAcceptedDecision ->
      CheckedClosureModeShapeAcceptedClassification
