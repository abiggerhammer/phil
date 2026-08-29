From Corelib Require Extraction.
From Phil.Core Require Import ProviderReplacementQualificationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ProviderReplacementQualificationKernel"
  ProviderReplacementDecision
  decideProviderReplacementByFacts
  ProviderReplacementReuseDecision
  decideProviderReplacementReuseByFacts.
