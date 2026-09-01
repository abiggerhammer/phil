From Stdlib Require Extraction.
From Phil.Core Require Import ProviderQualificationLineageCoreImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].

Extraction "ProviderQualificationLineageCoreKernel.hs"
  decideQualificationIdentityByFacts
  decideQualificationRegistryByFacts
  decideQualificationRootByFacts
  decideQualificationDependencyNodeByFacts
  propagateGroundPresence
  decideQualificationDependencyClosureByFacts.
