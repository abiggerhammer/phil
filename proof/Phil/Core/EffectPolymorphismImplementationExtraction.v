From Corelib Require Extraction.
From Phil.Core Require Import EffectPolymorphismImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "EffectPolymorphismKernel"
  decideEffectSetInstantiation.
