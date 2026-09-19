From Stdlib Require Import Bool.Bool.

Inductive ReviewR07Decision : Type :=
| ReviewR07Accepted
| ReviewR07Rejected.

Definition reviewR07Factsb
  (minusSeparate unaryAst unaryPrecedence binarySubtractDistinct
   signedExact floatStrict unsignedRejects : bool) : bool :=
  minusSeparate &&
  unaryAst &&
  unaryPrecedence &&
  binarySubtractDistinct &&
  signedExact &&
  floatStrict &&
  unsignedRejects.

Definition decideReviewR07
  (minusSeparate unaryAst unaryPrecedence binarySubtractDistinct
   signedExact floatStrict unsignedRejects : bool)
  : ReviewR07Decision :=
  if reviewR07Factsb
      minusSeparate unaryAst unaryPrecedence binarySubtractDistinct
      signedExact floatStrict unsignedRejects
  then ReviewR07Accepted
  else ReviewR07Rejected.

Theorem exact_review_r07_accepts :
  decideReviewR07 true true true true true true true =
    ReviewR07Accepted.
Proof. reflexivity. Qed.

Theorem folded_sign_or_missing_unary_node_rejects :
  decideReviewR07 false true true true true true true =
      ReviewR07Rejected /\
  decideReviewR07 true false true true true true true =
      ReviewR07Rejected.
Proof. split; reflexivity. Qed.

Theorem precedence_or_binary_subtraction_capture_rejects :
  decideReviewR07 true true false true true true true =
      ReviewR07Rejected /\
  decideReviewR07 true true true false true true true =
      ReviewR07Rejected.
Proof. split; reflexivity. Qed.

Theorem signed_or_float_semantic_drift_rejects :
  decideReviewR07 true true true true false true true =
      ReviewR07Rejected /\
  decideReviewR07 true true true true true false true =
      ReviewR07Rejected.
Proof. split; reflexivity. Qed.

Theorem unsigned_wrapping_negation_rejects :
  decideReviewR07 true true true true true true false =
    ReviewR07Rejected.
Proof. reflexivity. Qed.
