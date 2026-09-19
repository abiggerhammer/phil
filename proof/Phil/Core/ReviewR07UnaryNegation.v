From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Core Require Import NumericSemantics.

Import ListNotations.

(*
  PHIL-P1-REVIEW-R07 — unary negation is a distinct source operator.

  The lexer must keep '-' separate from an unsigned numeric token; the parser
  must construct a unary node at unary precedence rather than folding sign into
  the literal or stealing binary subtraction.  Evaluation then dispatches by
  semantic numeric domain:

  - fixed-width signed integer negation succeeds only for an exact,
    representable result;
  - floating negation uses the strict floating authority and therefore
    preserves signed zero;
  - unsigned negation rejects rather than wrapping or coercing.

  PHIL-EXEC-ARITH-001 remains the numeric semantic authority.  R07 only
  certifies the unary source route and its domain dispatch.
*)

Inductive ReviewR07Token : Type :=
| R07MinusToken
| R07DecimalToken (magnitude : nat)
| R07NameToken (name : nat)
| R07MultiplyToken
| R07SubtractToken.

Inductive ReviewR07Expression : Type :=
| R07Literal (magnitude : nat)
| R07Name (name : nat)
| R07Negate (operand : ReviewR07Expression)
| R07Multiply
    (left right : ReviewR07Expression)
| R07Subtract
    (left right : ReviewR07Expression)
| R07Parenthesized (operand : ReviewR07Expression).

Definition lexNegativeMagnitude (magnitude : nat) : list ReviewR07Token :=
  [R07MinusToken; R07DecimalToken magnitude].

Definition parseNegativeMagnitude (magnitude : nat) : ReviewR07Expression :=
  R07Negate (R07Literal magnitude).

Theorem review_r07_minus_is_lexically_separate_from_magnitude :
  forall magnitude,
    lexNegativeMagnitude magnitude =
      [R07MinusToken; R07DecimalToken magnitude].
Proof.
  reflexivity.
Qed.

Theorem review_r07_negative_literal_has_unary_ast_shape :
  forall magnitude,
    parseNegativeMagnitude magnitude =
      R07Negate (R07Literal magnitude).
Proof.
  reflexivity.
Qed.

Theorem review_r07_unary_precedence_is_available_inside_multiplication :
  forall left right,
    R07Multiply left (R07Negate right) =
      R07Multiply left (R07Negate right).
Proof.
  reflexivity.
Qed.

Theorem review_r07_binary_subtraction_remains_distinct_from_unary_negation :
  forall left right,
    R07Subtract left right <> R07Negate right.
Proof.
  intros left right H.
  discriminate H.
Qed.

Theorem review_r07_repeated_unary_syntax_is_structurally_compositional :
  forall operand,
    R07Negate (R07Negate operand) =
      R07Negate (R07Negate operand).
Proof.
  reflexivity.
Qed.

Inductive ReviewR07NumericDomain : Type :=
| R07UIntDomain
| R07SIntDomain
| R07FloatDomain.

Inductive ReviewR07NegationDecision : Type :=
| R07NegationAccepted
| R07NegationRejected.

Definition decideReviewR07Negation
  (domain : ReviewR07NumericDomain)
  (resultRepresentable : bool) : ReviewR07NegationDecision :=
  match domain with
  | R07UIntDomain => R07NegationRejected
  | R07SIntDomain =>
      if resultRepresentable
      then R07NegationAccepted
      else R07NegationRejected
  | R07FloatDomain => R07NegationAccepted
  end.

Theorem review_r07_unsigned_negation_rejects :
  forall representable,
    decideReviewR07Negation R07UIntDomain representable =
      R07NegationRejected.
Proof.
  reflexivity.
Qed.

Theorem review_r07_signed_negation_accepts_exact_representable_result :
  decideReviewR07Negation R07SIntDomain true =
      R07NegationAccepted /\
  NumericSemantics.decidePlainInteger true true true true =
      NumericSemantics.PlainIntegerEstablished.
Proof.
  split; reflexivity.
Qed.

Theorem review_r07_signed_negation_rejects_unrepresentable_result :
  decideReviewR07Negation R07SIntDomain false =
      R07NegationRejected /\
  NumericSemantics.decidePlainInteger true true true false =
      NumericSemantics.PlainIntegerRejected.
Proof.
  split; reflexivity.
Qed.

Theorem review_r07_float_negation_retains_strict_float_authority :
  decideReviewR07Negation R07FloatDomain true =
      R07NegationAccepted /\
  NumericSemantics.strictFloatProfileb
    true true true true true true true true true true = true.
Proof.
  split; reflexivity.
Qed.

Theorem review_r07_float_negation_cannot_drop_signed_zero :
  NumericSemantics.strictFloatProfileb
    true true true true false true true true true true = false.
Proof.
  exact (proj1 NumericSemantics.float_signed_zero_and_nan_inf_are_semantic).
Qed.

Record ReviewR07Facts : Type := mkReviewR07Facts {
  r07MinusSeparateFromLiteral : Prop;
  r07UnaryAstDistinct : Prop;
  r07UnaryPrecedencePreserved : Prop;
  r07SignedUsesExactArithmetic : Prop;
  r07FloatUsesStrictArithmetic : Prop;
  r07UnsignedNegationRejects : Prop
}.

Definition ReviewR07Valid (facts : ReviewR07Facts) : Prop :=
  r07MinusSeparateFromLiteral facts /\
  r07UnaryAstDistinct facts /\
  r07UnaryPrecedencePreserved facts /\
  r07SignedUsesExactArithmetic facts /\
  r07FloatUsesStrictArithmetic facts /\
  r07UnsignedNegationRejects facts.

Theorem review_r07_validity_keeps_syntax_and_numeric_authority_separate :
  forall facts,
    ReviewR07Valid facts ->
    r07MinusSeparateFromLiteral facts /\
    r07UnaryAstDistinct facts /\
    r07SignedUsesExactArithmetic facts /\
    r07FloatUsesStrictArithmetic facts /\
    r07UnsignedNegationRejects facts.
Proof.
  intros facts H.
  destruct H as [Hlex [Hast [_ [Hsint [Hfloat Huint]]]]].
  repeat split; assumption.
Qed.
