From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import NumericSemantics.

(*
  PHIL-EXEC-ARITH-001 — finite executable correspondence layer.

  The Haskell implementation has several independent authorities.  This file
  certifies the shared fail-closed shape without replacing their concrete
  arithmetic, IEEE bit-level, conversion, or StageContract logic.
*)

Inductive NumericGateDecision : Type :=
| NumericGateAccepted
| NumericGateRejected.

Definition decisionFromBool (accepted : bool) : NumericGateDecision :=
  if accepted then NumericGateAccepted else NumericGateRejected.

Theorem decision_from_bool_accept_iff_true :
  forall (accepted : bool),
    decisionFromBool accepted = NumericGateAccepted <-> accepted = true.
Proof.
  intros accepted.
  destruct accepted.
  - split; intros H.
    + reflexivity.
    + reflexivity.
  - split; intros H.
    + discriminate H.
    + discriminate H.
Qed.

Definition decideSignedDivisionGate
  (operandsValid divisorNonzero truncatesTowardZero pairedRemainder
    resultRepresentable : bool) : NumericGateDecision :=
  decisionFromBool
    (signedDivisionFactsb
      operandsValid divisorNonzero truncatesTowardZero pairedRemainder
      resultRepresentable).

Theorem signed_division_gate_accept_iff_exact_facts :
  forall (operandsValid divisorNonzero truncatesTowardZero pairedRemainder
    resultRepresentable : bool),
    decideSignedDivisionGate
      operandsValid divisorNonzero truncatesTowardZero pairedRemainder
      resultRepresentable = NumericGateAccepted <->
    signedDivisionFactsb
      operandsValid divisorNonzero truncatesTowardZero pairedRemainder
      resultRepresentable = true.
Proof.
  intros.
  apply decision_from_bool_accept_iff_true.
Qed.

Definition decideStrictFloatGate
  (formatExact storageWidthExact roundNearestTiesToEven gradualUnderflow
    signedZeroPreserved nanInfPreserved noReassociation noContraction
    noFlushToZero noApproximateArithmetic : bool) : NumericGateDecision :=
  decisionFromBool
    (strictFloatProfileb
      formatExact storageWidthExact roundNearestTiesToEven gradualUnderflow
      signedZeroPreserved nanInfPreserved noReassociation noContraction
      noFlushToZero noApproximateArithmetic).

Theorem strict_float_gate_accept_iff_exact_profile :
  forall (formatExact storageWidthExact roundNearestTiesToEven gradualUnderflow
    signedZeroPreserved nanInfPreserved noReassociation noContraction
    noFlushToZero noApproximateArithmetic : bool),
    decideStrictFloatGate
      formatExact storageWidthExact roundNearestTiesToEven gradualUnderflow
      signedZeroPreserved nanInfPreserved noReassociation noContraction
      noFlushToZero noApproximateArithmetic = NumericGateAccepted <->
    strictFloatProfileb
      formatExact storageWidthExact roundNearestTiesToEven gradualUnderflow
      signedZeroPreserved nanInfPreserved noReassociation noContraction
      noFlushToZero noApproximateArithmetic = true.
Proof.
  intros.
  apply decision_from_bool_accept_iff_true.
Qed.

Definition decideShiftGate
  (widthValid countInRange operandInRange resultRepresentable
    exactRightShiftSemantics noMaskedCount : bool) : NumericGateDecision :=
  decisionFromBool
    (shiftFactsb
      widthValid countInRange operandInRange resultRepresentable
      exactRightShiftSemantics noMaskedCount).

Theorem shift_gate_accept_iff_exact_facts :
  forall (widthValid countInRange operandInRange resultRepresentable
    exactRightShiftSemantics noMaskedCount : bool),
    decideShiftGate
      widthValid countInRange operandInRange resultRepresentable
      exactRightShiftSemantics noMaskedCount = NumericGateAccepted <->
    shiftFactsb
      widthValid countInRange operandInRange resultRepresentable
      exactRightShiftSemantics noMaskedCount = true.
Proof.
  intros.
  apply decision_from_bool_accept_iff_true.
Qed.

Definition decideNumericRealizationGate
  (exactWidths exactRounding noWrap noSaturate noTrapOrPoison
    noImplicitCast noReassociation noContraction preserveNanInf
    preserveSignedZero preserveGradualUnderflow noMaskedShift : bool)
  : NumericGateDecision :=
  decisionFromBool
    (numericRealizationFactsb
      exactWidths exactRounding noWrap noSaturate noTrapOrPoison
      noImplicitCast noReassociation noContraction preserveNanInf
      preserveSignedZero preserveGradualUnderflow noMaskedShift).

Theorem numeric_realization_gate_accept_iff_all_preservation_facts :
  forall (exactWidths exactRounding noWrap noSaturate noTrapOrPoison
    noImplicitCast noReassociation noContraction preserveNanInf
    preserveSignedZero preserveGradualUnderflow noMaskedShift : bool),
    decideNumericRealizationGate
      exactWidths exactRounding noWrap noSaturate noTrapOrPoison
      noImplicitCast noReassociation noContraction preserveNanInf
      preserveSignedZero preserveGradualUnderflow noMaskedShift =
      NumericGateAccepted <->
    numericRealizationFactsb
      exactWidths exactRounding noWrap noSaturate noTrapOrPoison
      noImplicitCast noReassociation noContraction preserveNanInf
      preserveSignedZero preserveGradualUnderflow noMaskedShift = true.
Proof.
  intros.
  apply decision_from_bool_accept_iff_true.
Qed.

Theorem production_plain_integer_unknown_is_not_silently_accepted :
  forall (exactResult resultRepresentable : bool),
    decidePlainInteger true false exactResult resultRepresentable =
      PlainIntegerRequiresProof.
Proof.
  apply plain_integer_symbolic_result_remains_explicit_proof_obligation.
Qed.

Theorem production_checked_integer_range_failure_is_explicit :
  decideCheckedInteger true false = CheckedIntegerTypedNegative.
Proof.
  apply checked_integer_out_of_range_is_source_visible_negative.
Qed.

Theorem production_implicit_numeric_conversion_rejects :
  forall (sourceValid targetValid partialitySatisfied resultRepresentable
    domainRulePreserved : bool),
    decideConversion
      false sourceValid targetValid partialitySatisfied resultRepresentable
      domainRulePreserved = ConversionRejectedImplicit.
Proof.
  apply numeric_conversion_must_be_explicit.
Qed.
