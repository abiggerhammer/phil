From Corelib Require Extraction.
From Phil.Core Require Import BoundaryProgressionImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "BoundaryProgressionKernel"
  decideReceiveProgressionByFacts
  decideEmissionDisposition
  planCompleteEmission
  decideSendProgressionByFacts.
