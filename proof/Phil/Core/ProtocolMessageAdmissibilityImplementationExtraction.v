From Corelib Require Extraction.
From Phil.Core Require Import ProtocolMessageAdmissibilityImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ProtocolMessageAdmissibilityKernel"
  decideBoundaryMessageContractByFacts
  decideIntrinsicBoundaryMessageByFact.
