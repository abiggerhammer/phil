From Stdlib Require Import Bool.Bool.

Inductive ReviewR06Decision : Type :=
| ReviewR06Accepted
| ReviewR06Rejected.

Definition reviewR06Factsb
  (strictChildOrderAuthorityValid
   receiveExactUsingBeforeOn
   receiveExactNoUsingAmountBeforeOn
   selectUsingBeforeOn
   selectNoUsingPayloadBeforeOn
   terminalUsingSuppressesLaterOn : bool) : bool :=
  strictChildOrderAuthorityValid &&
  receiveExactUsingBeforeOn &&
  receiveExactNoUsingAmountBeforeOn &&
  selectUsingBeforeOn &&
  selectNoUsingPayloadBeforeOn &&
  terminalUsingSuppressesLaterOn.

Definition decideReviewR06
  (strictChildOrderAuthorityValid
   receiveExactUsingBeforeOn
   receiveExactNoUsingAmountBeforeOn
   selectUsingBeforeOn
   selectNoUsingPayloadBeforeOn
   terminalUsingSuppressesLaterOn : bool)
  : ReviewR06Decision :=
  if reviewR06Factsb
      strictChildOrderAuthorityValid
      receiveExactUsingBeforeOn
      receiveExactNoUsingAmountBeforeOn
      selectUsingBeforeOn
      selectNoUsingPayloadBeforeOn
      terminalUsingSuppressesLaterOn
  then ReviewR06Accepted
  else ReviewR06Rejected.

Theorem exact_review_r06_accepts :
  decideReviewR06 true true true true true true =
    ReviewR06Accepted.
Proof. reflexivity. Qed.

Theorem missing_general_order_authority_rejects :
  decideReviewR06 false true true true true true =
    ReviewR06Rejected.
Proof. reflexivity. Qed.

Theorem receive_exact_order_drift_rejects :
  decideReviewR06 true false true true true true =
      ReviewR06Rejected /\
  decideReviewR06 true true false true true true =
      ReviewR06Rejected.
Proof. split; reflexivity. Qed.

Theorem select_order_drift_rejects :
  decideReviewR06 true true true false true true =
      ReviewR06Rejected /\
  decideReviewR06 true true true true false true =
      ReviewR06Rejected.
Proof. split; reflexivity. Qed.

Theorem terminal_using_suffix_execution_rejects :
  decideReviewR06 true true true true true false =
    ReviewR06Rejected.
Proof. reflexivity. Qed.
