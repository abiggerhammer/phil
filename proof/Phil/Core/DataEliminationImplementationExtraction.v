From Stdlib Require Import Extraction.
From Phil.Core Require Import Syntax DataElimination DataEliminationImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].

Extraction "DataEliminationKernel"
  decideFieldDispositionByMode
  decideEliminationPlanByFacts
  decideAggregateDispositionKind
  decideConsumingEliminationByFacts
  decideBorrowLifecycleByFacts.
