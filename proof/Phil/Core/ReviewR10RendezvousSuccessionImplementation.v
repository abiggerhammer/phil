From Stdlib Require Import Bool.Bool.

Inductive ReviewR10Decision : Type :=
| ReviewR10Accepted
| ReviewR10Rejected.

Definition reviewR10Factsb
  (firstRendezvousAccepted
   predecessorsConsumed
   exactSuccessorsInstalled
   successorStateCarriedForward
   secondRendezvousAccepted
   stalePredecessorRejected
   activationOnlyPathStillStrict : bool) : bool :=
  firstRendezvousAccepted &&
  predecessorsConsumed &&
  exactSuccessorsInstalled &&
  successorStateCarriedForward &&
  secondRendezvousAccepted &&
  stalePredecessorRejected &&
  activationOnlyPathStillStrict.

Definition decideReviewR10
  (firstRendezvousAccepted
   predecessorsConsumed
   exactSuccessorsInstalled
   successorStateCarriedForward
   secondRendezvousAccepted
   stalePredecessorRejected
   activationOnlyPathStillStrict : bool)
  : ReviewR10Decision :=
  if reviewR10Factsb
      firstRendezvousAccepted predecessorsConsumed exactSuccessorsInstalled
      successorStateCarriedForward secondRendezvousAccepted
      stalePredecessorRejected activationOnlyPathStillStrict
  then ReviewR10Accepted
  else ReviewR10Rejected.

Theorem exact_review_r10_accepts :
  decideReviewR10 true true true true true true true = ReviewR10Accepted.
Proof. reflexivity. Qed.

Theorem missing_exact_successor_handoff_rejects :
  decideReviewR10 true true true false true true true = ReviewR10Rejected.
Proof. reflexivity. Qed.

Theorem stale_predecessor_reuse_rejects :
  decideReviewR10 true true true true true false true = ReviewR10Rejected.
Proof. reflexivity. Qed.

Theorem initial_projection_checker_may_not_be_weakened_for_live_successors :
  decideReviewR10 true true true true true true false = ReviewR10Rejected.
Proof. reflexivity. Qed.
