From Stdlib Require Import Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

(*
  Shared-fuel monotonicity for the shift-refined effect-set payload after it is
  lifted through the full generic_requirement choice.

  Only alternative 6 is fuel-sensitive. The other twelve alternatives are
  preserved exactly, while the effects alternative delegates to the completed
  shift-refined effect_set_expression fuel-monotonicity theorem.

  Structural Rocq surface correspondence only. This does not prove
  derivation-driven totality for the full refined generic_requirement carrier,
  change Grammar-v1, Haskell/runtime behavior, evaluation semantics, or make
  broader parser soundness/completeness claims. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_monotone :
  forall fuel larger requirement refined,
    fuel <= larger ->
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel requirement = Some refined ->
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      larger requirement = Some refined.
Proof.
  intros fuel larger requirement refined Hle Hnormalize.
  destruct requirement; cbn in Hnormalize |- *.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effects)
      as [actual |] eqn:Heffects; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
        fuel larger effects actual Hle Heffects).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree
      tree)
    as [requirement |] eqn:Hrequirement; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.
