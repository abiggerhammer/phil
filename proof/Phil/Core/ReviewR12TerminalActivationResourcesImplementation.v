From Stdlib Require Import Bool.Bool.

Inductive ReviewR12Decision : Type :=
| ReviewR12Accepted
| ReviewR12Rejected.

Definition reviewR12Factsb
  (processCoverageExact
   activationResourcesExact
   nativeContextsPreserved
   runtimeInvariant
   runtimeNetworkExact : bool) : bool :=
  processCoverageExact &&
  activationResourcesExact &&
  nativeContextsPreserved &&
  runtimeInvariant &&
  runtimeNetworkExact.

Definition decideReviewR12
  (processCoverageExact
   activationResourcesExact
   nativeContextsPreserved
   runtimeInvariant
   runtimeNetworkExact : bool)
  : ReviewR12Decision :=
  if reviewR12Factsb
      processCoverageExact
      activationResourcesExact
      nativeContextsPreserved
      runtimeInvariant
      runtimeNetworkExact
  then ReviewR12Accepted
  else ReviewR12Rejected.

Theorem exact_review_r12_accepts :
  decideReviewR12 true true true true true = ReviewR12Accepted.
Proof. reflexivity. Qed.

Theorem missing_or_unexpected_process_context_rejects :
  decideReviewR12 false true true true true = ReviewR12Rejected.
Proof. reflexivity. Qed.

Theorem activation_resource_replacement_rejects :
  decideReviewR12 true false true true true = ReviewR12Rejected.
Proof. reflexivity. Qed.

Theorem native_context_reconstruction_rejects :
  decideReviewR12 true true false true true = ReviewR12Rejected.
Proof. reflexivity. Qed.

Theorem runtime_invariant_or_network_drift_rejects :
  decideReviewR12 true true true false true = ReviewR12Rejected /\
  decideReviewR12 true true true true false = ReviewR12Rejected.
Proof. split; reflexivity. Qed.
