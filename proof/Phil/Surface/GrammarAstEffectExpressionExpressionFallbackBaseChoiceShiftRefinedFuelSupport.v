From Stdlib Require Import Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

(*
  Shared-fuel monotonicity for the refined shift-expression lift through
  effect_expression.

  A successful refined term_arguments normalization remains successful when
  fuel is increased. This file lifts that fact through optional arguments,
  the effect-expression spine, and whole-tree normalization so a later
  derivation-totality proof can combine local witnesses with Nat.max.

  Structural Rocq surface-correspondence support only. This does not yet
  prove derivation-driven existence of a sufficient effect_expression fuel
  witness, change Grammar-v1 or evaluation semantics, or touch Haskell/runtime
  code. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel_monotone :
  forall fuel larger arguments refined,
    fuel <= larger ->
    phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel
      fuel arguments = Some refined ->
    phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel
      larger arguments = Some refined.
Proof.
  intros fuel larger [arguments_value |] refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel arguments_value)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
        fuel larger arguments_value actual Hle Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_monotone :
  forall fuel larger effect refined,
    fuel <= larger ->
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel effect = Some refined ->
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
      larger effect = Some refined.
Proof.
  intros fuel larger [reference arguments] refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel
      fuel arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel_monotone
      fuel larger arguments actual Hle Harguments).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree
      tree)
    as [effect |] eqn:Heffect; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.
