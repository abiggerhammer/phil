From Stdlib Require Extraction.
From Phil.Core Require Import SystemsControlPreservationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "SystemsControlPreservationKernel.hs"
  decideBranchPreservationByFacts
  decideStateProjectionByFacts
  decideProtocolPreservationByFacts
  decideBoundaryCommitByFacts
  decideSystemsControlByFacts.
