From Stdlib Require Import Extraction.
From Phil.Core Require Import DataSum DataSumImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "DataSumKernel"
  decideConstructorSelectionByFact
  decideSelectedPayloadRestorationByFacts
  decideContinuingArmByFact
  decideBranchConvergenceByFacts.
