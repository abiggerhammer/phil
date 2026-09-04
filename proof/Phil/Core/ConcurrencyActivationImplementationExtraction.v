From Corelib Require Extraction.
From Phil.Core Require Import ConcurrencyActivationImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ConcurrencyActivationKernel.hs"
  decideActivationBindingExplicitByFacts
  decideRestrictedInitialOwnershipByFacts
  decideDirectStatefulOwnershipByFacts
  decideActivationContextByFacts
  decideParticipantClassificationByFacts
  decideCertifiedConcurrencyActivationByFacts.
