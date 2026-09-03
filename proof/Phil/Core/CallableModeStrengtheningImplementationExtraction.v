From Corelib Require Extraction.
From Phil.Core Require Import CallableModeStrengtheningImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "CallableModeStrengtheningKernel"
  ExplicitClosureModeDecision
  decideExplicitClosureModeByFacts
  CheckedClosureModeShapeDecision
  decideCheckedClosureModeShapeByFacts.
