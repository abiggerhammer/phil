From Corelib Require Extraction.
From Phil.Core Require Import RuntimePrimitiveIdentityImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "RuntimePrimitiveIdentityKernel.hs"
  decideRuntimePrimitiveIdentityByFacts.
