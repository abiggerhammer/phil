From Corelib Require Extraction.
From Phil.Core Require Import GenericInstantiationValidityImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "GenericInstantiationValidityKernel"
  decideGenericDispositionValidity.
