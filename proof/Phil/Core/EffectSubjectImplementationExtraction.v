From Corelib Require Extraction.
From Phil.Core Require Import EffectSubjectImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "EffectSubjectKernel"
  decideEffectSubjectCorrespondence
  decideEffectSubjectRetarget.
