From Stdlib Require Extraction.
From Phil.Core Require Import ProviderQualificationLineageCoreImplementation.

Extraction Language Haskell.

Separate Extraction "ProviderQualificationLineageCoreKernel.hs"
  decideQualificationIdentityByFacts
  decideQualificationRegistryByFacts
  decideQualificationRootByFacts
  decideQualificationDependencyNodeByFacts
  propagateGroundPresence
  decideQualificationDependencyClosureByFacts.
