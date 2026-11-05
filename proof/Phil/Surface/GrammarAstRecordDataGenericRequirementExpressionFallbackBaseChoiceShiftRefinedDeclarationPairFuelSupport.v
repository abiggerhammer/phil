From Stdlib Require Import Arith.PeanoNat.
From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclarationFuelSupport.

Theorem
  phase1_surface_record_data_shift_refined_declaration_pair_shared_fuel :
  forall fuel1 fuel2 declaration1 declaration2 refined1 refined2,
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      fuel1 declaration1 = Some refined1 ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      fuel2 declaration2 = Some refined2 ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      (Nat.max fuel1 fuel2) declaration1 = Some refined1 /\
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      (Nat.max fuel1 fuel2) declaration2 = Some refined2.
Proof.
  intros fuel1 fuel2 declaration1 declaration2 refined1 refined2 H1 H2.
  split.
  - eapply phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_monotone.
    + apply Nat.le_max_l.
    + exact H1.
  - eapply phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_monotone.
    + apply Nat.le_max_r.
    + exact H2.
Qed.
