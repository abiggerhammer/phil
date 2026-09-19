From Stdlib Require Import Bool.Bool.

Inductive ReviewR02Decision : Type :=
| ReviewR02Accepted
| ReviewR02Rejected.

Definition reviewR02Factsb
  (llvmPreservationValid functionInventoryExact parameterCountExact
   parameterNamesExact parameterTypesExact parameterOrderExact : bool) : bool :=
  llvmPreservationValid &&
  functionInventoryExact &&
  parameterCountExact &&
  parameterNamesExact &&
  parameterTypesExact &&
  parameterOrderExact.

Definition decideReviewR02
  (llvmPreservationValid functionInventoryExact parameterCountExact
   parameterNamesExact parameterTypesExact parameterOrderExact : bool)
  : ReviewR02Decision :=
  if reviewR02Factsb
      llvmPreservationValid functionInventoryExact parameterCountExact
      parameterNamesExact parameterTypesExact parameterOrderExact
  then ReviewR02Accepted
  else ReviewR02Rejected.

Theorem exact_review_r02_accepts :
  decideReviewR02 true true true true true true =
    ReviewR02Accepted.
Proof. reflexivity. Qed.

Theorem predecessor_or_inventory_mismatch_rejects :
  decideReviewR02 false true true true true true =
      ReviewR02Rejected /\
  decideReviewR02 true false true true true true =
      ReviewR02Rejected.
Proof. split; reflexivity. Qed.

Theorem parameter_omission_rejects :
  decideReviewR02 true true false true true true =
    ReviewR02Rejected.
Proof. reflexivity. Qed.

Theorem parameter_name_or_type_drift_rejects :
  decideReviewR02 true true true false true true =
      ReviewR02Rejected /\
  decideReviewR02 true true true true false true =
      ReviewR02Rejected.
Proof. split; reflexivity. Qed.

Theorem parameter_order_drift_rejects :
  decideReviewR02 true true true true true false =
    ReviewR02Rejected.
Proof. reflexivity. Qed.
