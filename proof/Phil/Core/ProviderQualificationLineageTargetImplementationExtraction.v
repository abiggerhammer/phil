From Stdlib Require Extraction.
From Phil.Core Require Import ProviderQualificationLineageTargetImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ProviderQualificationLineageTargetKernel.hs"
  decideTargetReuseByFacts
  decideAdmissionApplicabilityByFacts.
