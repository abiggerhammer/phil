From Corelib Require Extraction.
From Phil.Core Require Import BoundaryCompleteRecognitionImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "BoundaryCompleteRecognitionKernel"
  decideCompleteExtentByFacts.
