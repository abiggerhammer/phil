From Stdlib Require Import Extraction.
From Phil.Core Require Import ResourceInvariantImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ResourceInvariantKernel"
  decideInvariantBoundaryByFacts.
