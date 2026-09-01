From Corelib Require Extraction.
From Phil.Core Require Import BoundarySubjectImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "BoundarySubjectKernel"
  decideBoundarySubjectTransferByFacts
  decideZeroCopyRealizationByFacts.
