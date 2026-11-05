From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstBaseExpressionChoiceSpine
  GrammarAstBaseExpressionShiftRefinedSpine
  GrammarAstShiftExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Consume the recursive grouping shift carrier at the base-expression choice.
   The command branch remains an exact ParseTree boundary. The new value stores
   neither the old choice carrier nor a duplicate original tree.

   Normalization uses the existing shallow base-choice decoder and the shift
   entry point's internally computed bounds. This structural translation does
   not interpret commands or establish production Haskell AST correspondence. *)

Inductive Phase1SurfaceBaseExpressionRecursiveGroupingSpine : Type :=
| Phase1BaseGroupingCommand (command : ParseTree)
| Phase1BaseGroupingShift
    (shift : Phase1SurfaceShiftExpressionRecursiveGroupingSpine).

Definition phase1_surface_base_expression_recursive_grouping_spine_base
  (expression : Phase1SurfaceBaseExpressionRecursiveGroupingSpine)
  : Phase1SurfaceBaseExpressionChoiceSpine :=
  match expression with
  | Phase1BaseGroupingCommand command => Phase1BaseExpressionCommand command
  | Phase1BaseGroupingShift shift =>
      Phase1BaseExpressionShift
        (phase1_surface_shift_expression_recursive_grouping_spine_tree shift)
  end.

Definition phase1_surface_base_expression_recursive_grouping_spine_tree
  (expression : Phase1SurfaceBaseExpressionRecursiveGroupingSpine)
  : ParseTree :=
  phase1_surface_base_expression_choice_spine_tree
    (phase1_surface_base_expression_recursive_grouping_spine_base expression).

Definition phase1_surface_normalize_base_expression_recursive_grouping_spine
  (expression : Phase1SurfaceBaseExpressionChoiceSpine)
  : option Phase1SurfaceBaseExpressionRecursiveGroupingSpine :=
  match expression with
  | Phase1BaseExpressionCommand command => Some (Phase1BaseGroupingCommand command)
  | Phase1BaseExpressionShift shift =>
      match phase1_surface_normalize_shift_expression_recursive_grouping_tree shift with
      | Some refined => Some (Phase1BaseGroupingShift refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_base_expression_recursive_grouping_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_base_expression_recursive_grouping_spine expression =
      Some refined ->
    phase1_surface_base_expression_recursive_grouping_spine_base refined =
      expression.
Proof.
  intros [command | shift] refined Hnormalize.
  - inversion Hnormalize; reflexivity.
  - cbn [phase1_surface_normalize_base_expression_recursive_grouping_spine]
      in Hnormalize.
    destruct
      (phase1_surface_normalize_shift_expression_recursive_grouping_tree shift)
      as [converted |] eqn:Hshift; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn [phase1_surface_base_expression_recursive_grouping_spine_base].
    rewrite
      (phase1_surface_normalize_shift_expression_recursive_grouping_tree_round_trip
        shift converted Hshift).
    reflexivity.
Qed.

Theorem phase1_surface_normalize_base_expression_recursive_grouping_spine_tree_round_trip :
  forall expression refined,
    phase1_surface_normalize_base_expression_recursive_grouping_spine expression =
      Some refined ->
    phase1_surface_base_expression_recursive_grouping_spine_tree refined =
      phase1_surface_base_expression_choice_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  unfold phase1_surface_base_expression_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_base_expression_recursive_grouping_spine_round_trip
      expression refined Hnormalize).
  reflexivity.
Qed.

Definition phase1_surface_normalize_base_expression_recursive_grouping_tree
  (tree : ParseTree)
  : option Phase1SurfaceBaseExpressionRecursiveGroupingSpine :=
  match phase1_surface_normalize_base_expression_choice_spine tree with
  | Some expression =>
      phase1_surface_normalize_base_expression_recursive_grouping_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_base_expression_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_base_expression_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_base_expression_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_base_expression_recursive_grouping_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_base_expression_choice_spine tree)
    as [expression |] eqn:Hchoice; try discriminate Hnormalize.
  rewrite
    (phase1_surface_normalize_base_expression_recursive_grouping_spine_tree_round_trip
      expression refined Hnormalize).
  exact
    (phase1_surface_normalize_base_expression_choice_spine_round_trip
      tree expression Hchoice).
Qed.

Definition phase1_surface_refine_base_expression_recursive_grouping
  (previous : Phase1SurfaceBaseExpressionShiftRefinedSpine)
  : option Phase1SurfaceBaseExpressionRecursiveGroupingSpine :=
  phase1_surface_normalize_base_expression_recursive_grouping_tree
    (phase1_surface_base_expression_shift_refined_spine_tree previous).

Theorem phase1_surface_refine_base_expression_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_base_expression_recursive_grouping previous =
      Some refined ->
    phase1_surface_base_expression_recursive_grouping_spine_tree refined =
      phase1_surface_base_expression_shift_refined_spine_tree previous.
Proof.
  intros previous refined Hnormalize.
  exact
    (phase1_surface_normalize_base_expression_recursive_grouping_tree_round_trip
      _ refined Hnormalize).
Qed.
