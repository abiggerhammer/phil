From Phil.Surface Require Import
  GrammarAstRecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTotality
  GrammarAstDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTotality
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclarationFuelSupport.

(*
  Derivation-driven finite-fuel totality for the record/data declaration-spine
  bridge introduced in #1499.

  A certified record_decl or data_decl selected tree obtains a finite fuel
  witness from the corresponding declaration-level totality theorem. The
  declaration-spine normalizer then preserves that refined declaration and its
  exact selected ParseTree.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  Haskell/runtime behavior, evaluation semantics, or claim broader parser
  soundness/completeness. Shared-fuel monotonicity from #1500 remains available
  for later aggregation across multiple declaration spines. This continues
  PHIL-SURFACE-GRAMMAR-CORR-001 after #1500.
*)

Lemma
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_total_from_record_derivation :
  forall path input rest declaration,
    phase1_declaration_spine_tag declaration = Phase1RecordDeclaration ->
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest (phase1_declaration_spine_selected_tree declaration) ->
    exists fuel refined,
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
        fuel declaration = Some refined /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_tree
        refined =
      phase1_declaration_spine_selected_tree declaration.
Proof.
  intros path input rest [tag selected_tree] Htag Hderive.
  cbn in Htag, Hderive |- *.
  destruct tag; try discriminate Htag.
  destruct
    (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation
      path input rest selected_tree Hderive)
    as [fuel [record [Hnormalize Htree]]].
  exists fuel,
    (Phase1RecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
      record).
  split.
  - cbn.
    rewrite Hnormalize.
    reflexivity.
  - cbn.
    exact Htree.
Qed.

Lemma
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_total_from_data_derivation :
  forall path input rest declaration,
    phase1_declaration_spine_tag declaration = Phase1DataDeclaration ->
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest (phase1_declaration_spine_selected_tree declaration) ->
    exists fuel refined,
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
        fuel declaration = Some refined /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_tree
        refined =
      phase1_declaration_spine_selected_tree declaration.
Proof.
  intros path input rest [tag selected_tree] Htag Hderive.
  cbn in Htag, Hderive |- *.
  destruct tag; try discriminate Htag.
  destruct
    (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation
      path input rest selected_tree Hderive)
    as [fuel [data_value [Hnormalize Htree]]].
  exists fuel,
    (Phase1DataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
      data_value).
  split.
  - cbn.
    rewrite Hnormalize.
    reflexivity.
  - cbn.
    exact Htree.
Qed.

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_total_from_derivation :
  forall path input rest declaration,
    (phase1_declaration_spine_tag declaration = Phase1RecordDeclaration /\
      Derives phase1_surface_rules path (ENonterminal "record_decl")
        input rest (phase1_declaration_spine_selected_tree declaration)) \/
    (phase1_declaration_spine_tag declaration = Phase1DataDeclaration /\
      Derives phase1_surface_rules path (ENonterminal "data_decl")
        input rest (phase1_declaration_spine_selected_tree declaration)) ->
    exists fuel refined,
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
        fuel declaration = Some refined /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_tree
        refined =
      phase1_declaration_spine_selected_tree declaration.
Proof.
  intros path input rest declaration Hderive.
  destruct Hderive as [[Htag Hrecord] | [Htag Hdata]].
  - eapply
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_total_from_record_derivation.
    + exact Htag.
    + exact Hrecord.
  - eapply
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_total_from_data_derivation.
    + exact Htag.
    + exact Hdata.
Qed.
