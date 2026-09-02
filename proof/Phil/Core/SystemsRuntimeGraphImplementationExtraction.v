From Phil.Core Require Import SystemsRuntimeGraphImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extraction "SystemsRuntimeGraphKernel.hs"
  decideRuntimeClaimGraphByFacts
  decideRuntimePrimitiveReuseByFacts
  decideRuntimeCostAttributionByFacts
  decideSystemsRuntimeGraphByFacts.
