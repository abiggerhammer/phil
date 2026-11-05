From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclarationTotality.

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel_total_from_declaration_derivation :
  forall path input rest top_level,
    (phase1_declaration_spine_tag (phase1_top_level_spine_declaration top_level) = Phase1RecordDeclaration /\
      Derives phase1_surface_rules path (ENonterminal "record_decl") input rest
        (phase1_declaration_spine_selected_tree (phase1_top_level_spine_declaration top_level))) \/
    (phase1_declaration_spine_tag (phase1_top_level_spine_declaration top_level) = Phase1DataDeclaration /\
      Derives phase1_surface_rules path (ENonterminal "data_decl") input rest
        (phase1_declaration_spine_selected_tree (phase1_top_level_spine_declaration top_level))) ->
    exists fuel refined,
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel fuel top_level = Some refined /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_tree refined =
      phase1_surface_top_level_spine_tree top_level.
Proof.
  intros path input rest [attributes declaration] Hderive.
  cbn in Hderive |- *.
  destruct
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_total_from_derivation
      path input rest declaration Hderive)
    as [fuel [refined_declaration [Hnormalize Htree]]].
  exists fuel.
  exists
    {| phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_attributes := attributes;
       phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_declaration := refined_declaration |}.
  assert
    (Htop :
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel
        fuel
        {| phase1_top_level_spine_attributes := attributes;
           phase1_top_level_spine_declaration := declaration |} =
      Some
        {| phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_attributes := attributes;
           phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_declaration := refined_declaration |}).
  { cbn. rewrite Hnormalize. reflexivity. }
  split.
  - exact Htop.
  - eapply
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel_round_trip.
    exact Htop.
Qed.
