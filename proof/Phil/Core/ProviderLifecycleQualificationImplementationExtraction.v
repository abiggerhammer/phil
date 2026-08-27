From Corelib Require Extraction.
From Phil.Core Require Import ProviderLifecycleQualificationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive prod => "(,)" [ "(,)" ].

Extraction "ProviderLifecycleQualificationKernel"
  memberb
  lifecyclePointEqualb
  checkProviderLifecycleObservation
  checkProviderLifecyclePoint
  decideProviderLifecycleQualification.
