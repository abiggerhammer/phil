From Stdlib Require Import Bool.Bool.

Inductive ReviewR09Decision : Type :=
| ReviewR09Accepted
| ReviewR09Rejected.

Definition reviewR09Factsb
  (integerZeroExact
   nonzeroZeroResultRounded
   finiteEqualityControlsPrecision
   negativeZeroExact
   negativeZeroSignPreserved
   numericConversionControlPreserved : bool) : bool :=
  integerZeroExact &&
  nonzeroZeroResultRounded &&
  finiteEqualityControlsPrecision &&
  negativeZeroExact &&
  negativeZeroSignPreserved &&
  numericConversionControlPreserved.

Definition decideReviewR09
  (integerZeroExact
   nonzeroZeroResultRounded
   finiteEqualityControlsPrecision
   negativeZeroExact
   negativeZeroSignPreserved
   numericConversionControlPreserved : bool)
  : ReviewR09Decision :=
  if reviewR09Factsb
      integerZeroExact
      nonzeroZeroResultRounded
      finiteEqualityControlsPrecision
      negativeZeroExact
      negativeZeroSignPreserved
      numericConversionControlPreserved
  then ReviewR09Accepted
  else ReviewR09Rejected.

Theorem exact_review_r09_accepts :
  decideReviewR09 true true true true true true =
    ReviewR09Accepted.
Proof. reflexivity. Qed.

Theorem integer_zero_misclassification_rejects :
  decideReviewR09 false true true true true true =
    ReviewR09Rejected.
Proof. reflexivity. Qed.

Theorem underflow_zero_false_exactness_rejects :
  decideReviewR09 true false true true true true =
    ReviewR09Rejected.
Proof. reflexivity. Qed.

Theorem ordinary_finite_precision_drift_rejects :
  decideReviewR09 true true false true true true =
    ReviewR09Rejected.
Proof. reflexivity. Qed.

Theorem signed_zero_precision_or_sign_drift_rejects :
  decideReviewR09 true true true false true true =
      ReviewR09Rejected /\
  decideReviewR09 true true true true false true =
      ReviewR09Rejected.
Proof. split; reflexivity. Qed.

Theorem predecessor_numeric_conversion_regression_rejects :
  decideReviewR09 true true true true true false =
    ReviewR09Rejected.
Proof. reflexivity. Qed.
