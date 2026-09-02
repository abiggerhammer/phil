From Stdlib Require Import Extraction.

From Phil.Systems Require Import IdentityImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "SystemsIdentityKernel"
  decideArtifactIdentityByFacts
  decideDecisionBindingByFacts.
