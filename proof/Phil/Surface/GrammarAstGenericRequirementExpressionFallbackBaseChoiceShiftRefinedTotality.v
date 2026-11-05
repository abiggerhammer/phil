From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceTotality
  GrammarAstGenericRequirementEffectsShiftRefinedTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Derivation-driven converse for the full thirteen-way shift-refined
  generic_requirement carrier.

  Alternative 6 reuses the isolated shift-refined
  "effects ... within ...;" totality result; the other twelve alternatives are
  already total because their payloads are preserved exactly by the lift.

  Structural Rocq surface correspondence only. This does not advance
  generic_requirements lists or declaration consumers, change Grammar-v1,
  Haskell/runtime behavior, evaluation semantics, or claim broader parser
  soundness/completeness. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation :
  forall requirement path input rest,
    Derives phase1_surface_rules path
      (ENonterminal "generic_requirement")
      input rest
      (phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
        requirement) ->
    exists fuel refined,
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel requirement = Some refined.
Proof.
  intros requirement path input rest Hderive.
  destruct requirement; cbn in Hderive |- *.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - destruct
      (phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel_total_from_derivation
        name_tree effects path input rest Hderive)
      as [fuel [isolated Hisolated]].
    unfold
      phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
      in Hisolated.
    destruct
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effects)
      as [refined_effects |] eqn:Heffects;
      try discriminate Hisolated.
    exists fuel.
    exists
      (Phase1GenericEffectsExpressionFallbackBaseChoiceShiftRefinedRequirement
        name_tree refined_effects).
    cbn.
    rewrite Heffects.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
  - exists 0.
    eexists.
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
      base path input rest Hcanonical)
    as [fuel [refined Hrefined]].
  assert (Hnormalize :
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined).
  {
    unfold
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel.
    rewrite Hbase.
    exact Hrefined.
  }
  exists fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
    exact Hnormalize.
Qed.
