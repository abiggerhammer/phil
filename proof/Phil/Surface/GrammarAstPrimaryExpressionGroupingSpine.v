From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionSpine
  GrammarAstParenthesizedExpressionSpineTotality
  GrammarAstTupleExpressionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the grouping payloads retained by the primary-expression outer spine.

    primary_expression =
        tuple_expression
      | parenthesized_expression
      | ...

  The tuple and parenthesized alternatives now carry their dedicated structural
  spines. The remaining primary-expression alternatives are retained exactly
  for later lexical/literal refinement. Nested ordinary-expression payloads
  inside the grouping carriers remain exact certified ParseTree values.
*)

Inductive Phase1SurfacePrimaryExpressionGroupingSpine : Type :=
| Phase1PrimaryExpressionTupleRefined
    (tuple_expression : Phase1SurfaceTupleExpressionSpine)
| Phase1PrimaryExpressionParenthesizedRefined
    (parenthesized : Phase1SurfaceParenthesizedExpressionSpine)
| Phase1PrimaryExpressionOtherRetained
    (branch : nat)
    (selected : ParseTree).

Definition phase1_surface_primary_expression_grouping_spine_tree
  (expression : Phase1SurfacePrimaryExpressionGroupingSpine) : ParseTree :=
  match expression with
  | Phase1PrimaryExpressionTupleRefined tuple_expression =>
      PTNonterminal "primary_expression"
        (PTAlternative 0
          (phase1_surface_tuple_expression_spine_tree tuple_expression))
  | Phase1PrimaryExpressionParenthesizedRefined parenthesized =>
      PTNonterminal "primary_expression"
        (PTAlternative 1
          (phase1_surface_parenthesized_expression_spine_tree parenthesized))
  | Phase1PrimaryExpressionOtherRetained branch selected =>
      PTNonterminal "primary_expression"
        (PTAlternative branch selected)
  end.

Definition phase1_surface_normalize_primary_expression_grouping_spine
  (expression : Phase1SurfacePrimaryExpressionSpine)
  : option Phase1SurfacePrimaryExpressionGroupingSpine :=
  let branch := phase1_primary_expression_spine_branch expression in
  let selected := phase1_primary_expression_spine_selected expression in
  match branch with
  | 0 =>
      match phase1_surface_normalize_tuple_expression_spine selected with
      | Some tuple_expression =>
          Some (Phase1PrimaryExpressionTupleRefined tuple_expression)
      | None => None
      end
  | 1 =>
      match phase1_surface_normalize_parenthesized_expression_spine selected with
      | Some parenthesized =>
          Some (Phase1PrimaryExpressionParenthesizedRefined parenthesized)
      | None => None
      end
  | _ =>
      Some (Phase1PrimaryExpressionOtherRetained branch selected)
  end.

Theorem
  phase1_surface_normalize_primary_expression_grouping_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_primary_expression_grouping_spine expression =
      Some refined ->
    phase1_surface_primary_expression_grouping_spine_tree refined =
      phase1_surface_primary_expression_spine_tree expression.
Proof.
  intros [branch selected] refined Hnormalize.
  destruct branch as [|branch].
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_tuple_expression_spine selected)
      as [tuple_expression |] eqn:Htuple; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_tuple_expression_spine_round_trip
        selected tuple_expression Htuple).
    reflexivity.
  - destruct branch as [|branch].
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_parenthesized_expression_spine selected)
        as [parenthesized |] eqn:Hparenthesized;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite
        (phase1_surface_normalize_parenthesized_expression_spine_round_trip
          selected parenthesized Hparenthesized).
      reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
Qed.

Definition phase1_surface_normalize_primary_expression_grouping_tree
  (tree : ParseTree)
  : option Phase1SurfacePrimaryExpressionGroupingSpine :=
  match phase1_surface_normalize_primary_expression_spine tree with
  | Some expression =>
      phase1_surface_normalize_primary_expression_grouping_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_primary_expression_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_primary_expression_grouping_tree tree =
      Some refined ->
    phase1_surface_primary_expression_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_primary_expression_grouping_tree in Hnormalize.
  destruct (phase1_surface_normalize_primary_expression_spine tree)
    as [expression |] eqn:Hexpression;
    try discriminate Hnormalize.
  transitivity (phase1_surface_primary_expression_spine_tree expression).
  - eapply
      phase1_surface_normalize_primary_expression_grouping_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_primary_expression_spine_round_trip.
    exact Hexpression.
Qed.
