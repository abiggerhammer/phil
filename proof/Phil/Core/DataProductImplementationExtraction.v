From Stdlib Require Import Extraction.
From Phil.Core Require Import DataProduct DataProductImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "DataProductKernel"
  decideProductEliminationByFacts
  decideProductRestorationByFacts.
