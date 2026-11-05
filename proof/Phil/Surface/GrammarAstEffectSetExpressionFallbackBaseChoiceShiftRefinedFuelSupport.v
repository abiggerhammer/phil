From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

(*
  Shared-fuel monotonicity for the refined shift-expression lift through
  effect_set_expression.

  A successful refined effect_expression normalization remains successful when
  fuel is increased. This file lifts that fact through finite effect-set member
  lists, effect-set literals, the enclosing effect_set_expression choice, and
  whole-tree normalization so a later derivation-totality proof can combine
  local witnesses under one shared Nat.max fuel bound.

  Structural Rocq surface-correspondence support only. This does not yet prove
  derivation-driven existence of a sufficient effect-set fuel witness, change
  Grammar-v1 or evaluation semantics, or touch Haskell/runtime code. It
  continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_monotone :
  forall fuel larger effects refined,
    fuel <= larger ->
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
      fuel effects = Some refined ->
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
      larger effects = Some refined.
Proof.
  intros fuel larger effects.
  induction effects as [|effect rest IH]; intros refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
        fuel rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
        fuel larger effect actual Hle Heffect).
    rewrite (IH actual_rest Hle Hrest).
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel_monotone :
  forall fuel larger literal refined,
    fuel <= larger ->
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
      fuel literal = Some refined ->
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
      larger literal = Some refined.
Proof.
  intros fuel larger [effects] refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
      fuel effects)
    as [actual |] eqn:Heffects; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_monotone
      fuel larger effects actual Hle Heffects).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_monotone :
  forall fuel larger effects refined,
    fuel <= larger ->
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel effects = Some refined ->
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
      larger effects = Some refined.
Proof.
  intros fuel larger effects refined Hle Hnormalize.
  destruct effects as [literal | reference].
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
        fuel literal)
      as [actual |] eqn:Hliteral; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel_monotone
        fuel larger literal actual Hle Hliteral).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_effect_set_expression_fallback_base_choice_tree tree)
    as [effects |] eqn:Heffects; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.
