From Stdlib Require Import Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclarationSpine
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

Lemma
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_monotone :
  forall fuel larger declaration refined,
    fuel <= larger ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      fuel declaration = Some refined ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      larger declaration = Some refined.
Proof.
  intros fuel larger [tag selected_tree] refined Hle Hnormalize.
  destruct tag; cbn in Hnormalize |- *; try discriminate Hnormalize.
  - destruct
      (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel selected_tree)
      as [record |] eqn:Hrecord; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_monotone
        fuel larger selected_tree record Hle Hrecord).
    reflexivity.
  - destruct
      (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel selected_tree)
      as [data_value |] eqn:Hdata; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_monotone
        fuel larger selected_tree data_value Hle Hdata).
    reflexivity.
Qed.
