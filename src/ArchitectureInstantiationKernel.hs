module ArchitectureInstantiationKernel where

import qualified Prelude

data ChildSlotDecision =
   ChildSlotAccepted
 | ChildSlotDuplicate

decideChildSlotByFacts :: Prelude.Bool -> ChildSlotDecision
decideChildSlotByFacts slotFresh =
  case slotFresh of {
   Prelude.True -> ChildSlotAccepted;
   Prelude.False -> ChildSlotDuplicate}

data ArchitectureRequirementDecision =
   ArchitectureRequirementAccepted
 | ArchitectureRequirementUnresolved
 | ArchitectureRequirementMissingBindingTarget
 | ArchitectureRequirementInterfaceMismatch

decideArchitectureRequirementByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        ArchitectureRequirementDecision
decideArchitectureRequirementByFacts hasExplicitDisposition isBoundTo targetExists interfaceMatches =
  case hasExplicitDisposition of {
   Prelude.True ->
    case isBoundTo of {
     Prelude.True ->
      case targetExists of {
       Prelude.True ->
        case interfaceMatches of {
         Prelude.True -> ArchitectureRequirementAccepted;
         Prelude.False -> ArchitectureRequirementInterfaceMismatch};
       Prelude.False -> ArchitectureRequirementMissingBindingTarget};
     Prelude.False -> ArchitectureRequirementAccepted};
   Prelude.False -> ArchitectureRequirementUnresolved}

decideRootRequirementByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool ->
                                ArchitectureRequirementDecision
decideRootRequirementByFacts =
  decideArchitectureRequirementByFacts

data ArchitectureReferenceDecision =
   ArchitectureReferenceAccepted
 | ArchitectureReferenceUnknownTarget

decideArchitectureReferenceByFacts :: Prelude.Bool ->
                                      ArchitectureReferenceDecision
decideArchitectureReferenceByFacts targetExists =
  case targetExists of {
   Prelude.True -> ArchitectureReferenceAccepted;
   Prelude.False -> ArchitectureReferenceUnknownTarget}

