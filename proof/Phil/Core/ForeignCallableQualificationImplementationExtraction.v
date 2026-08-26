From Corelib Require Extraction.
From Phil.Core Require Import ForeignCallableQualificationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].

Extraction "ForeignCallableQualificationKernel"
  decideForeignQualification.
