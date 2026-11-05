From Phil.Surface Require Import
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceTotality
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedTreeTotality.

Theorem
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_requirements"))
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "generic_requirements")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
        0 tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists 0, None.
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree_total_from_derivation
        path input rest tree Hderive)
      as [base_optional [Hbase_optional Hbase_round_trip]].
    destruct base_optional as [base |].
    + cbn in Hbase_round_trip.
      rewrite Hsome in Hbase_round_trip.
      inversion Hbase_round_trip; subst body.
      destruct
        (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
          base
          (descend path AtOptionalBody)
          input rest Hbody)
        as [fuel [refined Hrefined]].
      assert (Hnormalize :
        phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
          fuel tree = Some (Some refined)).
      {
        unfold
          phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel.
        rewrite Hbase_optional.
        cbn.
        rewrite Hrefined.
        reflexivity.
      }
      exists fuel, (Some refined).
      split.
      * exact Hnormalize.
      * eapply
          phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
        exact Hnormalize.
    + cbn in Hbase_round_trip.
      rewrite Hsome in Hbase_round_trip.
      discriminate Hbase_round_trip.
Qed.
