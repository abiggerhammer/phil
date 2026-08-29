From Corelib Require Extraction.
From Phil.Core Require Import ProviderReplacementQualificationImplementation.

Extraction Language Haskell.

Extraction "ProviderReplacementQualificationKernel"
  ProviderReplacementDecision
  decideProviderReplacementByFacts
  ProviderReplacementReuseDecision
  decideProviderReplacementReuseByFacts.
