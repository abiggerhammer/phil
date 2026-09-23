From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstBaseExpressionChoiceSpine
  GrammarAstShiftExpressionSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the refined shift_expression shell through the existing
  base_expression = command_expression | shift_expression choice.

  The command-expression branch remains an exact certified ParseTree.  Only
  the shift branch advances to Phase1SurfaceShiftExpressionSpine in this
  focused slice.
*)

Inductive Phase1SurfaceBaseExpressionShiftSpine : Type :=
| Phase1BaseExpressionShiftSpineCommand
    (command : ParseTree)
| Phase1BaseExpressionShiftSpineShift
    (shift : Phase1SurfaceShiftExpressionSpine).

Definition phase1_surface_base_expression_shift_spine_tree
  (expression : Phase1SurfaceBaseExpressionShiftSpine) : ParseTree :=
  match expression with
  | Phase1BaseExpressionShiftSpineCommand command =>
      PTNonterminal "base_expression"
        (PTAlternative 0 command)
  | Phase1BaseExpressionShiftSpineShift shift =>
      PTNonterminal "base_expression"
        (PTAlternative 1
          (phase1_surface_shift_expression_spine_tree shift))
  end.

Definition phase1_surface_normalize_base_expression_shift_spine
  (expression : Phase1SurfaceBaseExpressionChoiceSpine)
  : option Phase1SurfaceBaseExpressionShiftSpine :=
  match expression with
  | Phase1BaseExpressionCommand command =>
      Some (Phase1BaseExpressionShiftSpineCommand command)
  | Phase1BaseExpressionShift shift =>
      match phase1_surface_normalize_shift_expression_spine shift with
      | Some refined =>
          Some (Phase1BaseExpressionShiftSpineShift refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_base_expression_shift_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_base_expression_shift_spine expression =
      Some refined ->
    phase1_surface_base_expression_shift_spine_tree refined =
      phase1_surface_base_expression_choice_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [command | shift].
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_shift_expression_spine shift)
      as [actual |] eqn:Hshift; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_shift_expression_spine_round_trip
        shift actual Hshift).
    reflexivity.
Qed.

Definition phase1_surface_normalize_base_expression_shift_tree
  (tree : ParseTree) : option Phase1SurfaceBaseExpressionShiftSpine :=
  match phase1_surface_normalize_base_expression_choice_spine tree with
  | Some expression =>
      phase1_surface_normalize_base_expression_shift_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_base_expression_shift_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_base_expression_shift_tree tree = Some refined ->
    phase1_surface_base_expression_shift_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_base_expression_shift_tree in Hnormalize.
  destruct (phase1_surface_normalize_base_expression_choice_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity (phase1_surface_base_expression_choice_spine_tree expression).
  - eapply phase1_surface_normalize_base_expression_shift_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_base_expression_choice_spine_round_trip.
    exact Hexpression.
Qed.
