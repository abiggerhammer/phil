From Stdlib Require Import Bool.Bool.

Inductive ReviewR11Decision : Type :=
| ReviewR11Accepted
| ReviewR11Rejected.

Definition reviewR11Factsb
  (protocolAccepted
   leftOwnerUnique
   rightOwnerUnique
   leftOccurrencePreserved
   rightOccurrencePreserved
   leftSuccessorExact
   rightSuccessorExact : bool) : bool :=
  protocolAccepted &&
  leftOwnerUnique &&
  rightOwnerUnique &&
  leftOccurrencePreserved &&
  rightOccurrencePreserved &&
  leftSuccessorExact &&
  rightSuccessorExact.

Definition decideReviewR11
  (protocolAccepted
   leftOwnerUnique
   rightOwnerUnique
   leftOccurrencePreserved
   rightOccurrencePreserved
   leftSuccessorExact
   rightSuccessorExact : bool)
  : ReviewR11Decision :=
  if reviewR11Factsb
      protocolAccepted
      leftOwnerUnique
      rightOwnerUnique
      leftOccurrencePreserved
      rightOccurrencePreserved
      leftSuccessorExact
      rightSuccessorExact
  then ReviewR11Accepted
  else ReviewR11Rejected.

Theorem exact_review_r11_accepts :
  decideReviewR11 true true true true true true true =
    ReviewR11Accepted.
Proof. reflexivity. Qed.

Theorem missing_left_or_right_owner_rejects :
  decideReviewR11 true false true true true true true =
      ReviewR11Rejected /\
  decideReviewR11 true true false true true true true =
      ReviewR11Rejected.
Proof. split; reflexivity. Qed.

Theorem occurrence_identity_drift_rejects :
  decideReviewR11 true true true false true true true =
      ReviewR11Rejected /\
  decideReviewR11 true true true true false true true =
      ReviewR11Rejected.
Proof. split; reflexivity. Qed.

Theorem successor_name_drift_rejects :
  decideReviewR11 true true true true true false true =
      ReviewR11Rejected /\
  decideReviewR11 true true true true true true false =
      ReviewR11Rejected.
Proof. split; reflexivity. Qed.

Theorem protocol_acceptance_cannot_bypass_owner_ledger :
  decideReviewR11 true false false true true true true =
    ReviewR11Rejected.
Proof. reflexivity. Qed.
