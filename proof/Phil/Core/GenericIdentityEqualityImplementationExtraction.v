From Corelib Require Extraction.

From Phil.Core Require Import GenericIdentityEqualityImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "GenericIdentityEqualityKernel"
  sameApplicationFactsb
  decideGenericApplicationEquality
  sameDischargeLineageFactsb
  decideGenericDischargeLineageEquality.
