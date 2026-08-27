From Corelib Require Extraction.
From Phil.Core Require Import GenericInstantiationDomainImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].

Extraction "GenericInstantiationDomainKernel"
  keyIn
  keyListNoDupb
  allKeysInb
  exactKeyDomainb
  decideExactKeyDomain.
