From Corelib Require Extraction.
From Phil.Core Require Import GenericStaticKindImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "GenericStaticKindKernel"
  DirectStaticActualDecision
  decideDirectStaticActualByFact
  ReferencedStaticActualDecision
  decideReferencedStaticActualByFacts
  CheckedStaticActualShapeDecision
  decideCheckedStaticActualShapeByFacts.
