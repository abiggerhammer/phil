module SystemsGenericLoweringKernel where

import qualified Prelude

data GenericSystemsLoweringDecision =
   GenericSystemsLoweringAcceptedDecision
 | GenericSystemsLoweringContextRevisionDecision
 | GenericSystemsLoweringVerifierProfileDecision
 | GenericSystemsLoweringRealizationRefsDecision
 | GenericSystemsLoweringRealizationSemanticDecision
 | GenericSystemsLoweringResultCorrespondenceDecision
 | GenericSystemsLoweringStageClosureDecision

decideGenericSystemsLoweringByFacts :: Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       GenericSystemsLoweringDecision
decideGenericSystemsLoweringByFacts contextRevisionPresent verifierProfilePresent realizationRefsPresent realizationSemanticPresent resultMatchesModel stageClosureAccepted =
  case contextRevisionPresent of {
   Prelude.True ->
    case verifierProfilePresent of {
     Prelude.True ->
      case realizationRefsPresent of {
       Prelude.True ->
        case realizationSemanticPresent of {
         Prelude.True ->
          case resultMatchesModel of {
           Prelude.True ->
            case stageClosureAccepted of {
             Prelude.True -> GenericSystemsLoweringAcceptedDecision;
             Prelude.False -> GenericSystemsLoweringStageClosureDecision};
           Prelude.False ->
            GenericSystemsLoweringResultCorrespondenceDecision};
         Prelude.False -> GenericSystemsLoweringRealizationSemanticDecision};
       Prelude.False -> GenericSystemsLoweringRealizationRefsDecision};
     Prelude.False -> GenericSystemsLoweringVerifierProfileDecision};
   Prelude.False -> GenericSystemsLoweringContextRevisionDecision}

