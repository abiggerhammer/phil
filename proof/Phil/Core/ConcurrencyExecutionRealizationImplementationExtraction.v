From Corelib Require Extraction.
From Phil.Core Require Import ConcurrencyExecutionRealizationImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ConcurrencyExecutionRealizationKernel.hs"
  decideProcessDecisionRealizationByFacts
  decideEventCausalityRealizationByFacts
  decideSemanticPreservationRealizationByFacts
  decideTraceRealizationByFacts
  decideProcessExecutionRealizationByFacts.
