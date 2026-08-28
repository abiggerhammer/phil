From Corelib Require Extraction.

From Phil.Core Require Import CallableLifecycleImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "CallableLifecycleKernel.hs"
  CallablePreserveDecision
  decideCallablePreserve
  CallableConsumeDecision
  decideCallableConsume
  CallableReplaceDecision
  decideCallableReplace.
