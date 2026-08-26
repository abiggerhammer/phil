From Corelib Require Extraction.
From Phil.Core Require Import CallableLoweringImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "CallableLoweringKernel"
  decideCallableLowering.
