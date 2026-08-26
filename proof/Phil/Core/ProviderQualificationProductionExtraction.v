From Corelib Require Extraction.
From Phil.Core Require Import ProviderQualificationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive prod => "(,)" [ "(,)" ].

Extraction "ProviderQualificationKernel"
  decideOutcomeMapping
  decideOutcomeTraversal
  decideOperationTraversal
  decideOperationAt
  decideProviderQualification.
