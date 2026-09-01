From Stdlib Require Extraction.
From Phil.Core Require Import SystemsSubjectAuthorityImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "SystemsSubjectAuthorityKernel.hs"
  decideSubjectStageByFacts
  decideProviderCallStageByFacts
  decideEffectUseByFacts
  decideAuthorityExerciseByFacts
  decideAuthorityEffectStageByFacts.
