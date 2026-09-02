From Stdlib Require Import Extraction.

From Phil.Core Require Import ResourceJoinImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ResourceJoinKernel"
  decideResourceProjectionByFacts.
