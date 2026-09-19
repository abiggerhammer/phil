From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import NumericSemantics.

(*
  PHIL-P1-REVIEW-R08 — every raw known fixed-width signed value is range-checked
  before plain arithmetic/division may establish a result or residualize a
  proof obligation.

  PHIL-EXEC-ARITH-001 already owns exact mathematical arithmetic and
  representability.  R08 adds the raw-ingress ordering rule: malformed known
  terms are rejected during preflight and therefore cannot become symbolic
  proof obligations merely because another operand is unknown.
*)

Definition signedRangeFactsb
  (widthPositive valueAtOrAboveMinimum valueBelowExclusiveMaximum : bool)
  : bool :=
  widthPositive &&
  valueAtOrAboveMinimum &&
  valueBelowExclusiveMaximum.

Theorem exact_signed_range_accepts :
  signedRangeFactsb true true true = true.
Proof. reflexivity. Qed.

Theorem below_minimum_or_at_upper_bound_rejects :
  signedRangeFactsb true false true = false /\
  signedRangeFactsb true true false = false.
Proof. split; reflexivity. Qed.

Theorem nonpositive_signed_width_rejects :
  forall lower upper,
    signedRangeFactsb false lower upper = false.
Proof.
  intros lower upper.
  destruct lower, upper; reflexivity.
Qed.

Definition signedTermPreflightb
  (typeMatches rangeValid identityValid : bool) : bool :=
  typeMatches && rangeValid && identityValid.

Theorem malformed_known_term_fails_preflight :
  forall typeMatches identityValid,
    signedTermPreflightb typeMatches false identityValid = false.
Proof.
  intros typeMatches identityValid.
  destruct typeMatches, identityValid; reflexivity.
Qed.

Inductive PlainSignedDecision : Type :=
| PlainSignedEstablished
| PlainSignedRequiresProof
| PlainSignedRejected.

Definition decidePlainSigned
  (leftPreflight rightPreflight resultPreflight
   allKnown exactResult resultRepresentable : bool)
  : PlainSignedDecision :=
  if leftPreflight && rightPreflight && resultPreflight then
    if allKnown then
      if exactResult && resultRepresentable
      then PlainSignedEstablished
      else PlainSignedRejected
    else PlainSignedRequiresProof
  else PlainSignedRejected.

Theorem malformed_left_known_term_rejects_before_proof :
  forall rightPreflight resultPreflight allKnown exactResult resultRepresentable,
    decidePlainSigned
      false rightPreflight resultPreflight
      allKnown exactResult resultRepresentable =
    PlainSignedRejected.
Proof.
  intros.
  reflexivity.
Qed.

Theorem malformed_right_known_term_rejects_before_proof :
  forall leftPreflight resultPreflight allKnown exactResult resultRepresentable,
    decidePlainSigned
      leftPreflight false resultPreflight
      allKnown exactResult resultRepresentable =
    PlainSignedRejected.
Proof.
  intros leftPreflight resultPreflight allKnown exactResult resultRepresentable.
  destruct leftPreflight; reflexivity.
Qed.

Theorem malformed_known_result_rejects_before_proof :
  forall leftPreflight rightPreflight allKnown exactResult resultRepresentable,
    decidePlainSigned
      leftPreflight rightPreflight false
      allKnown exactResult resultRepresentable =
    PlainSignedRejected.
Proof.
  intros leftPreflight rightPreflight allKnown exactResult resultRepresentable.
  destruct leftPreflight, rightPreflight; reflexivity.
Qed.

Theorem proof_residualization_requires_all_raw_terms_valid :
  forall leftPreflight rightPreflight resultPreflight exactResult resultRepresentable,
    decidePlainSigned
      leftPreflight rightPreflight resultPreflight
      false exactResult resultRepresentable =
      PlainSignedRequiresProof ->
    leftPreflight = true /\
    rightPreflight = true /\
    resultPreflight = true.
Proof.
  intros leftPreflight rightPreflight resultPreflight exactResult resultRepresentable H.
  destruct leftPreflight, rightPreflight, resultPreflight;
    simpl in H; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem fully_known_exact_representable_signed_case_establishes :
  decidePlainSigned true true true true true true =
      PlainSignedEstablished /\
  NumericSemantics.decidePlainInteger true true true true =
      NumericSemantics.PlainIntegerEstablished.
Proof.
  split; reflexivity.
Qed.

Theorem fully_known_unrepresentable_result_rejects :
  decidePlainSigned true true true true true false =
      PlainSignedRejected /\
  NumericSemantics.decidePlainInteger true true true false =
      NumericSemantics.PlainIntegerRejected.
Proof.
  split; reflexivity.
Qed.

Definition rawSignedIngressb
  (typeMatches rangeValid : bool) : bool :=
  typeMatches && rangeValid.

Inductive RawSignedIngressDecision : Type :=
| RawSignedIngressAccepted
| RawSignedIngressRejected.

Definition decideRawSignedIngress
  (typeMatches rangeValid : bool) : RawSignedIngressDecision :=
  if rawSignedIngressb typeMatches rangeValid
  then RawSignedIngressAccepted
  else RawSignedIngressRejected.

Theorem checked_signed_division_rejects_malformed_raw_literal :
  forall typeMatches,
    decideRawSignedIngress typeMatches false =
      RawSignedIngressRejected.
Proof.
  intros typeMatches.
  destruct typeMatches; reflexivity.
Qed.

Theorem numeric_conversion_rejects_malformed_signed_source :
  forall typeMatches,
    decideRawSignedIngress typeMatches false =
      RawSignedIngressRejected.
Proof.
  intros typeMatches.
  destruct typeMatches; reflexivity.
Qed.

Record ReviewR08Facts : Type := mkReviewR08Facts {
  r08ArithmeticPreflightBeforeDecision : Prop;
  r08DivisionPreflightBeforeDecision : Prop;
  r08ProofResidualizationOnlyAfterPreflight : Prop;
  r08CheckedDivisionValidatesRawIngress : Prop;
  r08ConversionValidatesRawIngress : Prop
}.

Definition ReviewR08Valid (facts : ReviewR08Facts) : Prop :=
  r08ArithmeticPreflightBeforeDecision facts /\
  r08DivisionPreflightBeforeDecision facts /\
  r08ProofResidualizationOnlyAfterPreflight facts /\
  r08CheckedDivisionValidatesRawIngress facts /\
  r08ConversionValidatesRawIngress facts.

Theorem review_r08_keeps_raw_range_validation_before_authority :
  forall facts,
    ReviewR08Valid facts ->
    r08ArithmeticPreflightBeforeDecision facts /\
    r08DivisionPreflightBeforeDecision facts /\
    r08ProofResidualizationOnlyAfterPreflight facts.
Proof.
  intros facts H.
  destruct H as [Ha [Hd [Hp _]]].
  repeat split; assumption.
Qed.
