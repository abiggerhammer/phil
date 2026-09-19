From Stdlib Require Import Bool.Bool.

Inductive ReviewR03Decision : Type :=
| ReviewR03Accepted
| ReviewR03Rejected.

Definition reviewR03Factsb
  (llvmPreservationValid selectedLowererFunctionInventoryExact : bool) : bool :=
  llvmPreservationValid &&
  selectedLowererFunctionInventoryExact.

Definition decideReviewR03
  (llvmPreservationValid selectedLowererFunctionInventoryExact : bool)
  : ReviewR03Decision :=
  if reviewR03Factsb
      llvmPreservationValid
      selectedLowererFunctionInventoryExact
  then ReviewR03Accepted
  else ReviewR03Rejected.

Theorem exact_review_r03_accepts :
  decideReviewR03 true true = ReviewR03Accepted.
Proof. reflexivity. Qed.

Theorem predecessor_preservation_failure_rejects :
  decideReviewR03 false true = ReviewR03Rejected.
Proof. reflexivity. Qed.

Theorem unadvertised_or_omitted_function_rejects :
  decideReviewR03 true false = ReviewR03Rejected.
Proof. reflexivity. Qed.

Theorem explicitly_selected_helper_remains_admissible :
  decideReviewR03 true true = ReviewR03Accepted.
Proof. reflexivity. Qed.
