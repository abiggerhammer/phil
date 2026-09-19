From Stdlib Require Import Bool.Bool.

Inductive ReviewR08Decision : Type :=
| ReviewR08Accepted
| ReviewR08Rejected.

Definition reviewR08Factsb
  (arithmeticKnownTermsRangeChecked
   divisionKnownTermsRangeChecked
   malformedKnownCannotResidualize
   exactBoundaryValuesAccepted
   checkedDivisionRawIngressChecked
   conversionRawIngressChecked : bool) : bool :=
  arithmeticKnownTermsRangeChecked &&
  divisionKnownTermsRangeChecked &&
  malformedKnownCannotResidualize &&
  exactBoundaryValuesAccepted &&
  checkedDivisionRawIngressChecked &&
  conversionRawIngressChecked.

Definition decideReviewR08
  (arithmeticKnownTermsRangeChecked
   divisionKnownTermsRangeChecked
   malformedKnownCannotResidualize
   exactBoundaryValuesAccepted
   checkedDivisionRawIngressChecked
   conversionRawIngressChecked : bool)
  : ReviewR08Decision :=
  if reviewR08Factsb
      arithmeticKnownTermsRangeChecked
      divisionKnownTermsRangeChecked
      malformedKnownCannotResidualize
      exactBoundaryValuesAccepted
      checkedDivisionRawIngressChecked
      conversionRawIngressChecked
  then ReviewR08Accepted
  else ReviewR08Rejected.

Theorem exact_review_r08_accepts :
  decideReviewR08 true true true true true true =
    ReviewR08Accepted.
Proof. reflexivity. Qed.

Theorem arithmetic_or_division_preflight_gap_rejects :
  decideReviewR08 false true true true true true =
      ReviewR08Rejected /\
  decideReviewR08 true false true true true true =
      ReviewR08Rejected.
Proof. split; reflexivity. Qed.

Theorem malformed_known_residualization_rejects :
  decideReviewR08 true true false true true true =
    ReviewR08Rejected.
Proof. reflexivity. Qed.

Theorem boundary_drift_rejects :
  decideReviewR08 true true true false true true =
    ReviewR08Rejected.
Proof. reflexivity. Qed.

Theorem checked_division_or_conversion_raw_ingress_gap_rejects :
  decideReviewR08 true true true true false true =
      ReviewR08Rejected /\
  decideReviewR08 true true true true true false =
      ReviewR08Rejected.
Proof. split; reflexivity. Qed.
