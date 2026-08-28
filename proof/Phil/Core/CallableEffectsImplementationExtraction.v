From Stdlib Require Import Extraction.

From Phil.Core Require Import CallableEffectsImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "CallableEffectKernel.hs"
  CallableUseEffectKind
  callableUseEffectKindContributesPublicBound
  CallableEffectBoundDecision
  decideCallableEffectBound
  effectDeltaBit.
