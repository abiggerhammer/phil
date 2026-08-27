From Stdlib Require Import Extraction.

From Phil.Core Require Import CallableEffectsImplementation.

Extraction Language Haskell.

Extraction "CallableEffectKernel.hs"
  CallableUseEffectKind
  callableUseEffectKindContributesPublicBound
  CallableEffectBoundDecision
  decideCallableEffectBound
  effectDeltaBit.
