From Stdlib Require Import Extraction.

From Phil.Core Require Import ResourceLoopImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ResourceLoopKernel"
  decideLoopProjectionByFacts
  decideStateTransportByFacts.
