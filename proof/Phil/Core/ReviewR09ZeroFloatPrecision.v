From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import NumericSemantics.

(*
  PHIL-P1-REVIEW-R09 — zero-result float conversion precision classification.

  PHIL-EXEC-ARITH-001 owns strict IEEE-format semantics and exact conversion
  authority.  R09 closes one classification edge case in explicit numeric
  conversion: producing floating zero is not by itself enough to call a
  conversion exact.

  For finite conversion:
  - exact source zero -> floating zero is Exact;
  - nonzero source -> floating zero is Rounded;
  - a nonzero finite target is Exact iff its exact rational value equals the
    source value, otherwise Rounded.

  Floating +/-0 converted across F32/F64 is a separate exact class conversion
  and must preserve its zero sign.
*)

Inductive ReviewR09Precision : Type :=
| R09Exact
| R09Rounded.

Definition classifyFiniteFloatPrecision
  (sourceExactZero targetIsZero finiteTargetEqualsExactSource : bool)
  : ReviewR09Precision :=
  if targetIsZero then
    if sourceExactZero then R09Exact else R09Rounded
  else
    if finiteTargetEqualsExactSource then R09Exact else R09Rounded.

Theorem integer_zero_to_float_zero_is_exact :
  classifyFiniteFloatPrecision true true false = R09Exact.
Proof. reflexivity. Qed.

Theorem nonzero_underflow_to_float_zero_is_rounded :
  classifyFiniteFloatPrecision false true false = R09Rounded.
Proof. reflexivity. Qed.

Theorem nonzero_exact_finite_conversion_is_exact :
  classifyFiniteFloatPrecision false false true = R09Exact.
Proof. reflexivity. Qed.

Theorem nonzero_inexact_finite_conversion_is_rounded :
  classifyFiniteFloatPrecision false false false = R09Rounded.
Proof. reflexivity. Qed.

Theorem zero_output_precision_depends_on_exact_source_zero :
  forall sourceExactZero finiteTargetEqualsExactSource,
    classifyFiniteFloatPrecision
      sourceExactZero true finiteTargetEqualsExactSource =
    if sourceExactZero then R09Exact else R09Rounded.
Proof.
  intros sourceExactZero finiteTargetEqualsExactSource.
  destruct sourceExactZero; reflexivity.
Qed.

Inductive ReviewR09ZeroSign : Type :=
| R09PositiveZero
| R09NegativeZero.

Record ReviewR09FloatZeroConversion : Type := mkReviewR09FloatZeroConversion {
  r09SourceZeroSign : ReviewR09ZeroSign;
  r09TargetZeroSign : ReviewR09ZeroSign;
  r09ZeroPrecision : ReviewR09Precision
}.

Definition ExactSignedZeroConversion
  (conversion : ReviewR09FloatZeroConversion) : Prop :=
  r09TargetZeroSign conversion = r09SourceZeroSign conversion /\
  r09ZeroPrecision conversion = R09Exact.

Theorem positive_zero_width_conversion_is_exact_and_sign_preserving :
  ExactSignedZeroConversion
    (mkReviewR09FloatZeroConversion
      R09PositiveZero R09PositiveZero R09Exact).
Proof.
  split; reflexivity.
Qed.

Theorem negative_zero_width_conversion_is_exact_and_sign_preserving :
  ExactSignedZeroConversion
    (mkReviewR09FloatZeroConversion
      R09NegativeZero R09NegativeZero R09Exact).
Proof.
  split; reflexivity.
Qed.

Theorem zero_sign_drift_is_not_exact_signed_zero_conversion :
  ~ ExactSignedZeroConversion
      (mkReviewR09FloatZeroConversion
        R09NegativeZero R09PositiveZero R09Exact).
Proof.
  intros H.
  destruct H as [Hsign _].
  discriminate Hsign.
Qed.

Record ReviewR09Facts : Type := mkReviewR09Facts {
  r09FiniteZeroUsesExactSourceValue : Prop;
  r09NonzeroUnderflowRemainsRounded : Prop;
  r09FiniteEqualityControlsPrecision : Prop;
  r09SignedZeroClassConversionExact : Prop;
  r09SignedZeroSignPreserved : Prop;
  r09StrictFloatAuthorityRetained : Prop
}.

Definition ReviewR09Valid (facts : ReviewR09Facts) : Prop :=
  r09FiniteZeroUsesExactSourceValue facts /\
  r09NonzeroUnderflowRemainsRounded facts /\
  r09FiniteEqualityControlsPrecision facts /\
  r09SignedZeroClassConversionExact facts /\
  r09SignedZeroSignPreserved facts /\
  r09StrictFloatAuthorityRetained facts.

Theorem review_r09_keeps_zero_classification_and_float_authority_distinct :
  forall facts,
    ReviewR09Valid facts ->
    r09FiniteZeroUsesExactSourceValue facts /\
    r09NonzeroUnderflowRemainsRounded facts /\
    r09SignedZeroClassConversionExact facts /\
    r09SignedZeroSignPreserved facts /\
    r09StrictFloatAuthorityRetained facts.
Proof.
  intros facts H.
  destruct H as [Hzero [Hunder [_ [Hexact [Hsign Hstrict]]]]].
  repeat split; assumption.
Qed.

Theorem review_r09_retains_strict_signed_zero_semantics :
  NumericSemantics.strictFloatProfileb
    true true true true true true true true true true = true.
Proof. reflexivity. Qed.
