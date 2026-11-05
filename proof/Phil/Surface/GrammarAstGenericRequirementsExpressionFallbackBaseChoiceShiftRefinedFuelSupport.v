From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

Import ListNotations.

(*
  Shared-fuel monotonicity for the shift-refined generic_requirements lift.

  The preceding slice lifts the completed thirteen-way shift-refined
  generic_requirement carrier through finite generic_requirements lists and
  their optional wrapper using one explicit fuel value. This file proves that
  every successful normalization at a given fuel remains successful at any
  larger fuel, first across the finite requirement list and then through the
  enclosing list, optional, and whole-tree normalizers.

  Structural Rocq surface correspondence only. This does not yet prove
  derivation-driven existence of a sufficient common fuel witness for a
  generic_requirements list, advance declaration consumers, change Grammar-v1,
  Haskell/runtime behavior, evaluation semantics, or make broader parser
  soundness/completeness claims. It continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1492.
*)

Lemma
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel_monotone :
  forall fuel larger requirements refined,
    fuel <= larger ->
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
      fuel requirements = Some refined ->
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
      larger requirements = Some refined.
Proof.
  intros fuel larger requirements.
  induction requirements as [|requirement rest IH];
    intros refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel requirement)
      as [actual |] eqn:Hrequirement; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
        fuel rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
        fuel larger requirement actual Hle Hrequirement).
    rewrite (IH actual_rest Hle Hrest).
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel_monotone :
  forall fuel larger requirements refined,
    fuel <= larger ->
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel requirements = Some refined ->
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
      larger requirements = Some refined.
Proof.
  intros fuel larger [requirements] refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
      fuel requirements)
    as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel_monotone
      fuel larger requirements actual Hle Hrequirements).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_monotone :
  forall fuel larger requirements refined,
    fuel <= larger ->
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      fuel requirements = Some refined ->
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      larger requirements = Some refined.
Proof.
  intros fuel larger [requirements |] refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel requirements)
      as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
        fuel larger requirements actual Hle Hrequirements).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_tree
      tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree
      tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.
