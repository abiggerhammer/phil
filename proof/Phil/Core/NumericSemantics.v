From Stdlib Require Import Bool.Bool.

(*
  PHIL-EXEC-ARITH-001 — exact fixed-width integer, signed division/remainder,
  strict floating, explicit conversion, exact shift, and realization-preservation
  semantics.

  This file is deliberately representation-neutral.  It states the semantic
  gates already enforced by the Phase-1 Haskell authorities without importing
  host Integer/Float/Double representation, Text serialization, or backend
  instruction behavior into the theorem statement.
*)

Inductive PlainIntegerDecision : Type :=
| PlainIntegerEstablished
| PlainIntegerRequiresProof
| PlainIntegerRejected.

Definition decidePlainInteger
  (wellTyped known exactResult resultRepresentable : bool)
  : PlainIntegerDecision :=
  if wellTyped then
    if known then
      if andb exactResult resultRepresentable
      then PlainIntegerEstablished
      else PlainIntegerRejected
    else PlainIntegerRequiresProof
  else PlainIntegerRejected.

Theorem plain_integer_symbolic_result_remains_explicit_proof_obligation :
  forall (exactResult resultRepresentable : bool),
    decidePlainInteger true false exactResult resultRepresentable =
      PlainIntegerRequiresProof.
Proof.
  reflexivity.
Qed.

Theorem plain_integer_known_exact_representable_result_is_established :
  decidePlainInteger true true true true = PlainIntegerEstablished.
Proof.
  reflexivity.
Qed.

Theorem plain_integer_never_repairs_mismatch_or_out_of_range_result :
  decidePlainInteger true true false true = PlainIntegerRejected /\
  decidePlainInteger true true true false = PlainIntegerRejected.
Proof.
  split; reflexivity.
Qed.

Theorem plain_integer_wrong_domain_or_width_rejects :
  forall (known exactResult resultRepresentable : bool),
    decidePlainInteger false known exactResult resultRepresentable =
      PlainIntegerRejected.
Proof.
  reflexivity.
Qed.

Inductive CheckedIntegerDecision : Type :=
| CheckedIntegerSucceeded
| CheckedIntegerTypedNegative
| CheckedIntegerRejected.

Definition decideCheckedInteger
  (operandsValid resultRepresentable : bool) : CheckedIntegerDecision :=
  if operandsValid then
    if resultRepresentable
    then CheckedIntegerSucceeded
    else CheckedIntegerTypedNegative
  else CheckedIntegerRejected.

Theorem checked_integer_out_of_range_is_source_visible_negative :
  decideCheckedInteger true false = CheckedIntegerTypedNegative.
Proof.
  reflexivity.
Qed.

Theorem checked_integer_valid_representable_result_succeeds :
  decideCheckedInteger true true = CheckedIntegerSucceeded.
Proof.
  reflexivity.
Qed.

Theorem checked_integer_invalid_operand_is_not_coerced :
  decideCheckedInteger false true = CheckedIntegerRejected.
Proof.
  reflexivity.
Qed.

Definition signedDivisionFactsb
  (operandsValid divisorNonzero truncatesTowardZero pairedRemainder
    resultRepresentable : bool) : bool :=
  andb operandsValid
    (andb divisorNonzero
      (andb truncatesTowardZero
        (andb pairedRemainder resultRepresentable))).

Theorem signed_division_exact_contract_accepts :
  signedDivisionFactsb true true true true true = true.
Proof.
  reflexivity.
Qed.

Theorem signed_division_zero_divisor_cannot_satisfy_success_contract :
  signedDivisionFactsb true false true true true = false.
Proof.
  reflexivity.
Qed.

Theorem signed_division_requires_truncation_toward_zero_and_paired_remainder :
  signedDivisionFactsb true true false true true = false /\
  signedDivisionFactsb true true true false true = false.
Proof.
  split; reflexivity.
Qed.

Theorem signed_division_unrepresentable_result_cannot_succeed :
  signedDivisionFactsb true true true true false = false.
Proof.
  reflexivity.
Qed.

Definition strictFloatProfileb
  (formatExact storageWidthExact roundNearestTiesToEven gradualUnderflow
    signedZeroPreserved nanInfPreserved noReassociation noContraction
    noFlushToZero noApproximateArithmetic : bool) : bool :=
  andb formatExact
    (andb storageWidthExact
      (andb roundNearestTiesToEven
        (andb gradualUnderflow
          (andb signedZeroPreserved
            (andb nanInfPreserved
              (andb noReassociation
                (andb noContraction
                  (andb noFlushToZero noApproximateArithmetic)))))))).

Theorem strict_float_profile_accepts_only_exact_phase1_profile :
  strictFloatProfileb
    true true true true true true true true true true = true.
Proof.
  reflexivity.
Qed.

Theorem float_wrong_rounding_or_flush_to_zero_rejects :
  strictFloatProfileb
    true true false true true true true true true true = false /\
  strictFloatProfileb
    true true true true true true true true false true = false.
Proof.
  split; reflexivity.
Qed.

Theorem float_reassociation_contraction_or_approximation_rejects :
  strictFloatProfileb
    true true true true true true false true true true = false /\
  strictFloatProfileb
    true true true true true true true false true true = false /\
  strictFloatProfileb
    true true true true true true true true true false = false.
Proof.
  repeat split; reflexivity.
Qed.

Theorem float_signed_zero_and_nan_inf_are_semantic :
  strictFloatProfileb
    true true true true false true true true true true = false /\
  strictFloatProfileb
    true true true true true false true true true true = false.
Proof.
  split; reflexivity.
Qed.

Inductive ConversionDecision : Type :=
| ConversionAccepted
| ConversionTypedNegative
| ConversionRejectedImplicit.

Definition decideConversion
  (explicitConversion sourceValid targetValid partialitySatisfied
    resultRepresentable domainRulePreserved : bool) : ConversionDecision :=
  if explicitConversion then
    if andb sourceValid
        (andb targetValid
          (andb partialitySatisfied
            (andb resultRepresentable domainRulePreserved)))
    then ConversionAccepted
    else ConversionTypedNegative
  else ConversionRejectedImplicit.

Theorem numeric_conversion_must_be_explicit :
  forall (sourceValid targetValid partialitySatisfied resultRepresentable
    domainRulePreserved : bool),
    decideConversion
      false sourceValid targetValid partialitySatisfied resultRepresentable
      domainRulePreserved = ConversionRejectedImplicit.
Proof.
  reflexivity.
Qed.

Theorem exact_conversion_accepts :
  decideConversion true true true true true true = ConversionAccepted.
Proof.
  reflexivity.
Qed.

Theorem fractional_nonfinite_or_out_of_range_partial_conversion_is_explicit_negative :
  decideConversion true true true false true true = ConversionTypedNegative /\
  decideConversion true true true true false true = ConversionTypedNegative /\
  decideConversion true true true true true false = ConversionTypedNegative.
Proof.
  repeat split; reflexivity.
Qed.

Definition shiftFactsb
  (widthValid countInRange operandInRange resultRepresentable
    exactRightShiftSemantics noMaskedCount : bool) : bool :=
  andb widthValid
    (andb countInRange
      (andb operandInRange
        (andb resultRepresentable
          (andb exactRightShiftSemantics noMaskedCount)))).

Theorem exact_shift_contract_accepts :
  shiftFactsb true true true true true true = true.
Proof.
  reflexivity.
Qed.

Theorem shift_count_is_never_masked :
  shiftFactsb true false true true true true = false /\
  shiftFactsb true true true true true false = false.
Proof.
  split; reflexivity.
Qed.

Theorem signed_right_shift_keeps_its_distinct_floor_semantics :
  shiftFactsb true true true true false true = false.
Proof.
  reflexivity.
Qed.

Theorem left_shift_may_not_discard_high_bits :
  shiftFactsb true true true false true true = false.
Proof.
  reflexivity.
Qed.

Definition numericRealizationFactsb
  (exactWidths exactRounding noWrap noSaturate noTrapOrPoison
    noImplicitCast noReassociation noContraction preserveNanInf
    preserveSignedZero preserveGradualUnderflow noMaskedShift : bool) : bool :=
  andb exactWidths
    (andb exactRounding
      (andb noWrap
        (andb noSaturate
          (andb noTrapOrPoison
            (andb noImplicitCast
              (andb noReassociation
                (andb noContraction
                  (andb preserveNanInf
                    (andb preserveSignedZero
                      (andb preserveGradualUnderflow noMaskedShift)))))))))).

Theorem exact_numeric_realization_profile_accepts :
  numericRealizationFactsb
    true true true true true true true true true true true true = true.
Proof.
  reflexivity.
Qed.

Theorem target_wrap_saturation_or_poison_cannot_refine_plain_semantics :
  numericRealizationFactsb
    true true false true true true true true true true true true = false /\
  numericRealizationFactsb
    true true true false true true true true true true true true = false /\
  numericRealizationFactsb
    true true true true false true true true true true true true = false.
Proof.
  repeat split; reflexivity.
Qed.

Theorem target_implicit_cast_or_masked_shift_cannot_refine_source_semantics :
  numericRealizationFactsb
    true true true true true false true true true true true true = false /\
  numericRealizationFactsb
    true true true true true true true true true true true false = false.
Proof.
  split; reflexivity.
Qed.

Theorem target_float_weakening_cannot_refine_strict_float_semantics :
  numericRealizationFactsb
    true true true true true true false true true true true true = false /\
  numericRealizationFactsb
    true true true true true true true false true true true true = false /\
  numericRealizationFactsb
    true true true true true true true true false true true true = false /\
  numericRealizationFactsb
    true true true true true true true true true false true true = false /\
  numericRealizationFactsb
    true true true true true true true true true true false true = false.
Proof.
  repeat split; reflexivity.
Qed.
