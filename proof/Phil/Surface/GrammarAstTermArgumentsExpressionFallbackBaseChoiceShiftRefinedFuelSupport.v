From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstShiftExpressionRefinedSpineFuelSupport.

Import ListNotations.

(*
  Shared-fuel support for the term_arguments lift of completed refined
  shift expressions.

  The term_arguments carrier introduced in the immediately preceding slice
  applies one common fuel value to every argument. This file proves the
  monotonicity needed to raise successful local fuel witnesses to a common
  Nat.max fuel: first through the completed shift-expression carrier, then
  through base_expression and expression, and finally across the finite
  term-argument list.

  Structural Rocq surface-correspondence support only. This does not yet
  prove derivation-driven existence of a sufficient common fuel witness for
  term_arguments, change Grammar-v1 or evaluation semantics, or touch
  Haskell/runtime code. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_shift_expression_first_refined_spine_fuel_monotone :
  forall fuel larger expression refined,
    fuel <= larger ->
    phase1_surface_normalize_shift_expression_first_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_normalize_shift_expression_first_refined_spine_fuel
      larger expression = Some refined.
Proof.
  intros fuel larger expression refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_shift_expression_first_refined_spine_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_additive_expression_refined_tree_fuel
      fuel
      (phase1_shift_expression_spine_first expression))
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_additive_expression_refined_tree_fuel_monotone
      fuel larger
      (phase1_shift_expression_spine_first expression)
      first Hle Hfirst).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_shift_expression_first_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_shift_expression_first_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_shift_expression_first_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_shift_expression_first_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_shift_expression_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_shift_expression_first_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_shift_expression_refined_spine_fuel_monotone :
  forall fuel larger expression refined,
    fuel <= larger ->
    phase1_surface_normalize_shift_expression_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_normalize_shift_expression_refined_spine_fuel
      larger expression = Some refined.
Proof.
  intros fuel larger expression refined Hle Hnormalize.
  unfold phase1_surface_normalize_shift_expression_refined_spine_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_shift_suffix_refined_spines_fuel
      fuel
      (phase1_shift_expression_first_refined_spine_rest expression))
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_shift_suffix_refined_spines_fuel_monotone
      fuel larger
      (phase1_shift_expression_first_refined_spine_rest expression)
      rest Hle Hrest).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_shift_expression_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_shift_expression_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_shift_expression_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold phase1_surface_normalize_shift_expression_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_shift_expression_first_refined_tree_fuel
      fuel tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_shift_expression_first_refined_tree_fuel_monotone
      fuel larger tree expression Hle Hexpression)
    as Hexpression_larger.
  rewrite Hexpression_larger.
  eapply phase1_surface_normalize_shift_expression_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_base_expression_shift_refined_spine_fuel_monotone :
  forall fuel larger expression refined,
    fuel <= larger ->
    phase1_surface_normalize_base_expression_shift_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_normalize_base_expression_shift_refined_spine_fuel
      larger expression = Some refined.
Proof.
  intros fuel larger expression refined Hle Hnormalize.
  destruct expression as [command | shift].
  - cbn in Hnormalize |- *.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_shift_expression_refined_tree_fuel
        fuel
        (phase1_surface_shift_expression_spine_tree shift))
      as [refined_shift |] eqn:Hshift; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_shift_expression_refined_tree_fuel_monotone
        fuel larger
        (phase1_surface_shift_expression_spine_tree shift)
        refined_shift Hle Hshift).
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel_monotone :
  forall fuel larger expression refined,
    fuel <= larger ->
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel
      larger expression = Some refined.
Proof.
  intros fuel larger expression refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_base_expression_shift_refined_spine_fuel
      fuel
      (phase1_expression_fallback_base_choice_shift_spine_base expression))
    as [base |] eqn:Hbase; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_base_expression_shift_refined_spine_fuel_monotone
      fuel larger
      (phase1_expression_fallback_base_choice_shift_spine_base expression)
      base Hle Hbase).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_monotone :
  forall fuel larger expression refined,
    fuel <= larger ->
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
      larger expression = Some refined.
Proof.
  intros fuel larger expression refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_shift_spine
      expression)
    as [shifted |] eqn:Hshifted; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_monotone :
  forall fuel larger arguments refined,
    fuel <= larger ->
    phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
      fuel arguments = Some refined ->
    phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
      larger arguments = Some refined.
Proof.
  intros fuel larger arguments.
  induction arguments as [|argument rest IH];
    intros refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
        fuel argument)
      as [refined_argument |] eqn:Hargument; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
        fuel rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    pose proof
      (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_monotone
        fuel larger argument refined_argument Hle Hargument)
      as Hargument_larger.
    pose proof
      (IH refined_rest Hle Hrest)
      as Hrest_larger.
    rewrite Hargument_larger, Hrest_larger.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel_monotone :
  forall fuel larger arguments refined,
    fuel <= larger ->
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel arguments = Some refined ->
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
      larger arguments = Some refined.
Proof.
  intros fuel larger [arguments] refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
      fuel arguments)
    as [values |] eqn:Hvalues; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_monotone
      fuel larger arguments values Hle Hvalues).
  reflexivity.
Qed.
