From Stdlib Require Import Extraction.
From Phil.Core Require Import DataModeImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].

Extraction "DataModeKernel"
  modeLub
  deriveRecordMode
  deriveSumMode
  resolvedStrongestMode
  decideRecordModeByCandidate
  decideSumModeByCandidate
  decideNominalModeByFact
  decideAggregateFormationByFact.
