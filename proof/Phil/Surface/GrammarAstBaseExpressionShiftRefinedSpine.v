From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstBaseExpressionShiftSpine
  GrammarAstShiftExpressionRefinedSpine.

Import ListNotations.
Open Scope string_scope.

Inductive Phase1SurfaceBaseExpressionShiftRefinedSpine : Type :=
| Phase1BaseExpressionShiftRefinedCommand
    (command : ParseTree)
| Phase1BaseExpressionShiftRefinedShift
    (shift : Phase1SurfaceShiftExpressionRefinedSpine).

Definition phase1_surface_base_expression_shift_refined_spine_tree
  (expression : Phase1SurfaceBaseExpressionShiftRefinedSpine) : ParseTree :=
  match expression with
  | Phase1BaseExpressionShiftRefinedCommand command =>
      PTNonterminal "base_expression" (PTAlternative 0 command)
  | Phase1BaseExpressionShiftRefinedShift shift =>
      PTNonterminal "base_expression"
        (PTAlternative 1
          (phase1_surface_shift_expression_refined_spine_tree shift))
  end.

Definition phase1_surface_normalize_base_expression_shift_refined_spine_fuel
  (fuel : nat)
  (expression : Phase1SurfaceBaseExpressionShiftSpine)
  : option Phase1SurfaceBaseExpressionShiftRefinedSpine :=
  match expression with
  | Phase1BaseExpressionShiftSpineCommand command =>
      Some (Phase1BaseExpressionShiftRefinedCommand command)
  | Phase1BaseExpressionShiftSpineShift shift =>
      match
        phase1_surface_normalize_shift_expression_refined_tree_fuel
          fuel
          (phase1_surface_shift_expression_spine_tree shift)
      with
      | Some refined => Some (Phase1BaseExpressionShiftRefinedShift refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_base_expression_shift_refined_spine_fuel_round_trip :
  forall fuel expression refined,
    phase1_surface_normalize_base_expression_shift_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_base_expression_shift_refined_spine_tree refined =
      phase1_surface_base_expression_shift_spine_tree expression.
Proof.
  intros fuel expression refined Hnormalize.
  destruct expression as [command | shift].
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_shift_expression_refined_tree_fuel
        fuel
        (phase1_surface_shift_expression_spine_tree shift))
      as [refined_shift |] eqn:Hshift; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_shift_expression_refined_tree_fuel_round_trip
        fuel
        (phase1_surface_shift_expression_spine_tree shift)
        refined_shift
        Hshift).
    reflexivity.
Qed.

Definition phase1_surface_normalize_base_expression_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceBaseExpressionShiftRefinedSpine :=
  match phase1_surface_normalize_base_expression_shift_tree tree with
  | Some expression =>
      phase1_surface_normalize_base_expression_shift_refined_spine_fuel
        fuel expression
  | None => None
  end.

Theorem phase1_surface_normalize_base_expression_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_base_expression_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_base_expression_shift_refined_spine_tree refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold phase1_surface_normalize_base_expression_shift_refined_tree_fuel
    in Hnormalize.
  destruct (phase1_surface_normalize_base_expression_shift_tree tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity (phase1_surface_base_expression_shift_spine_tree expression).
  - eapply
      phase1_surface_normalize_base_expression_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_base_expression_shift_tree_round_trip.
    exact Hexpression.
Qed.
