module ConcurrencyExecutionRealizationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideProcessDecisionRealizationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool -> Prelude.Bool
decideProcessDecisionRealizationByFacts processCoverage noEmptyExecution decisionCoverage costExplicit assumptionsDeclared =
  andb processCoverage
    (andb noEmptyExecution
      (andb decisionCoverage (andb costExplicit assumptionsDeclared)))

decideEventCausalityRealizationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool
decideEventCausalityRealizationByFacts eventCoverage noEmptyEvent eventInjective causalityPreserved =
  andb eventCoverage
    (andb noEmptyEvent (andb eventInjective causalityPreserved))

decideSemanticPreservationRealizationByFacts :: Prelude.Bool -> Prelude.Bool
                                                -> Prelude.Bool ->
                                                Prelude.Bool -> Prelude.Bool
                                                -> Prelude.Bool
decideSemanticPreservationRealizationByFacts ownersExact factsExact factsDeclared terminalExact assumptionsExact =
  andb ownersExact
    (andb factsExact
      (andb factsDeclared (andb terminalExact assumptionsExact)))

decideTraceRealizationByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                 -> Prelude.Bool
decideTraceRealizationByFacts processTrace eventTrace causalityTrace =
  andb processTrace (andb eventTrace causalityTrace)

decideProcessExecutionRealizationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                            Prelude.Bool -> Prelude.Bool ->
                                            Prelude.Bool
decideProcessExecutionRealizationByFacts processDecision eventCausality semanticPreservation traceExplicit =
  andb processDecision
    (andb eventCausality (andb semanticPreservation traceExplicit))

