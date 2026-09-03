From Corelib Require Extraction.
From Phil.Core Require Import CallableOutcomeFidelity CallableOutcomeImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "CallableOutcomeKernel"
  OutcomeBucket
  ResidualDisposition
  CallableOutcomeDecision
  decideCallableOutcomeByFacts.
