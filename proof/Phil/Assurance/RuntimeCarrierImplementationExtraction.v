From Corelib Require Extraction.
From Phil.Assurance Require Import RuntimeCarrierImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "RuntimeCarrierKernel"
  decideExactCarrierBindingByFacts
  decideCoveredCarrierUseByFacts
  decideExplicitBoundaryCarrierUseByFacts
  decidePreservedCarrierTransitionByFacts
  decideReplacedCarrierTransitionByFacts
  decideClosedCarrierTransitionByFacts.
