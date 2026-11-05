From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedFuelSupport
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTotality.

Import ListNotations.
Open Scope string_scope.

Lemma
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel_total_from_spine_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ENonterminal "generic_requirement" ->
    forall requirements,
      trees =
        map
          phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
          requirements ->
      exists fuel refined,
        phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
          fuel requirements = Some refined.
Proof.
  intros path body input rest trees Hderive Hbody_shape.
  subst body.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros requirements Htrees.
  - destruct requirements as [|requirement requirements]; cbn in Htrees.
    + exists 0, [].
      reflexivity.
    + discriminate Htrees.
  - destruct requirements as [|requirement requirements]; cbn in Htrees;
      try discriminate Htrees.
    inversion Htrees; subst tree trees.
    destruct
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
        requirement
        (descend path AtRepetitionBody)
        input middle Hitem)
      as [fuel [refined Hrefined]].
    destruct (IHrest requirements eq_refl)
      as [rest_fuel [refined_rest Hrefined_rest]].
    exists (Nat.max fuel rest_fuel), (refined :: refined_rest).
    cbn.
    rewrite
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
        fuel (Nat.max fuel rest_fuel) requirement refined
        (Nat.le_max_l fuel rest_fuel) Hrefined).
    rewrite
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel_monotone
        rest_fuel (Nat.max fuel rest_fuel) requirements refined_rest
        (Nat.le_max_r fuel rest_fuel) Hrefined_rest).
    reflexivity.
Qed.
