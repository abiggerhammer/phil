module CallableModeStrengtheningKernel where

import qualified Prelude

data ExplicitClosureModeDecision =
   ExplicitClosureModeWeakeningDecision
 | ExplicitClosureModeEqualDecision
 | ExplicitClosureModeMissingJustificationDecision
 | ExplicitClosureModeTargetImplementationDecision
 | ExplicitClosureModeWrongContractDecision
 | ExplicitClosureModeEmptyJustificationDecision
 | ExplicitClosureModeStrengthenedDecision

decideExplicitClosureModeByFacts :: Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    ExplicitClosureModeDecision
decideExplicitClosureModeByFacts nonWeakening equalToMinimum justificationPresent targetImplementationReason contractMatches detailPresent =
  case nonWeakening of {
   Prelude.True ->
    case equalToMinimum of {
     Prelude.True -> ExplicitClosureModeEqualDecision;
     Prelude.False ->
      case justificationPresent of {
       Prelude.True ->
        case targetImplementationReason of {
         Prelude.True -> ExplicitClosureModeTargetImplementationDecision;
         Prelude.False ->
          case contractMatches of {
           Prelude.True ->
            case detailPresent of {
             Prelude.True -> ExplicitClosureModeStrengthenedDecision;
             Prelude.False -> ExplicitClosureModeEmptyJustificationDecision};
           Prelude.False -> ExplicitClosureModeWrongContractDecision}};
       Prelude.False -> ExplicitClosureModeMissingJustificationDecision}};
   Prelude.False -> ExplicitClosureModeWeakeningDecision}

data CheckedClosureModeShapeDecision =
   CheckedClosureModeMinimumDecision
 | CheckedClosureModeSelectedDecision
 | CheckedClosureModeJustificationDecision
 | CheckedClosureModeShapeAcceptedDecision

decideCheckedClosureModeShapeByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool ->
                                        CheckedClosureModeShapeDecision
decideCheckedClosureModeShapeByFacts minimumExact selectedExact justificationExact =
  case minimumExact of {
   Prelude.True ->
    case selectedExact of {
     Prelude.True ->
      case justificationExact of {
       Prelude.True -> CheckedClosureModeShapeAcceptedDecision;
       Prelude.False -> CheckedClosureModeJustificationDecision};
     Prelude.False -> CheckedClosureModeSelectedDecision};
   Prelude.False -> CheckedClosureModeMinimumDecision}

