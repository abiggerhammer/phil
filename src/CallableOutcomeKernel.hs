module CallableOutcomeKernel where

import qualified Prelude

data OutcomeBucket =
   OutcomePostconditionBucket
 | OutcomeAssumptionBucket
 | OutcomeEffectBucket
 | OutcomeDischargedFactBucket

data ResidualDisposition =
   ResidualExact
 | ResidualReclassified OutcomeBucket
 | ResidualMismatch

data CallableOutcomeDecision =
   CallableOutcomeClassSetDecision
 | CallableOutcomeStateDecision
 | CallableOutcomeCalleeTransitionDecision
 | CallableResidualObligationReclassifiedDecision OutcomeBucket
 | CallableResidualObligationMismatchDecision
 | CallableOutcomePostconditionDecision
 | CallableOutcomeAssumptionDecision
 | CallableOutcomeEffectDecision
 | CallableOutcomeDischargedFactDecision
 | CallableOutcomeAcceptedDecision

decideCallableOutcomeByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool -> Prelude.Bool ->
                                Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> ResidualDisposition ->
                                CallableOutcomeDecision
decideCallableOutcomeByFacts classDomainExact stateExact transitionExact residualExact postconditionsExact assumptionsExact effectsExact dischargedFactsExact residualDisposition =
  case classDomainExact of {
   Prelude.True ->
    case stateExact of {
     Prelude.True ->
      case transitionExact of {
       Prelude.True ->
        case residualDisposition of {
         ResidualExact ->
          case residualExact of {
           Prelude.True ->
            case postconditionsExact of {
             Prelude.True ->
              case assumptionsExact of {
               Prelude.True ->
                case effectsExact of {
                 Prelude.True ->
                  case dischargedFactsExact of {
                   Prelude.True -> CallableOutcomeAcceptedDecision;
                   Prelude.False -> CallableOutcomeDischargedFactDecision};
                 Prelude.False -> CallableOutcomeEffectDecision};
               Prelude.False -> CallableOutcomeAssumptionDecision};
             Prelude.False -> CallableOutcomePostconditionDecision};
           Prelude.False -> CallableResidualObligationMismatchDecision};
         ResidualReclassified bucket ->
          CallableResidualObligationReclassifiedDecision bucket;
         ResidualMismatch -> CallableResidualObligationMismatchDecision};
       Prelude.False -> CallableOutcomeCalleeTransitionDecision};
     Prelude.False -> CallableOutcomeStateDecision};
   Prelude.False -> CallableOutcomeClassSetDecision}
