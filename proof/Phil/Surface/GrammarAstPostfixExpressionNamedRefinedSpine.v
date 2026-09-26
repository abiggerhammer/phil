From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixExpressionRefinedTailSpine
  GrammarAstPostfixExpressionSpine.

Import ListNotations.
Open Scope string_scope.

Inductive Phase1SurfacePostfixExpressionNamedRefinedSpine : Type :=
| Phase1SurfacePostfixExpressionNamedRefined
    (named : Phase1SurfaceNamedPostfixExpressionRefinedTailSpine)
| Phase1SurfacePostfixExpressionPrimaryRetained
    (primary : ParseTree)
    (projections : list string).

Definition phase1_surface_postfix_expression_named_refined_spine_tree
  (expression : Phase1SurfacePostfixExpressionNamedRefinedSpine) : ParseTree :=
  match expression with
  | Phase1SurfacePostfixExpressionNamedRefined named =>
      PTNonterminal "postfix_expression"
        (PTAlternative 0
          (phase1_surface_named_postfix_expression_refined_tail_spine_tree named))
  | Phase1SurfacePostfixExpressionPrimaryRetained primary projections =>
      phase1_surface_postfix_expression_spine_tree
        (Phase1SurfacePostfixExpressionPrimary primary projections)
  end.

Definition phase1_surface_normalize_postfix_expression_named_refined_spine
  (expression : Phase1SurfacePostfixExpressionSpine)
  : option Phase1SurfacePostfixExpressionNamedRefinedSpine :=
  match expression with
  | Phase1SurfacePostfixExpressionNamed named_tree =>
      match
        phase1_surface_normalize_named_postfix_expression_refined_tail_tree
          named_tree
      with
      | Some named =>
          Some (Phase1SurfacePostfixExpressionNamedRefined named)
      | None => None
      end
  | Phase1SurfacePostfixExpressionPrimary primary projections =>
      Some
        (Phase1SurfacePostfixExpressionPrimaryRetained
          primary projections)
  end.

Theorem
  phase1_surface_normalize_postfix_expression_named_refined_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_postfix_expression_named_refined_spine expression =
      Some refined ->
    phase1_surface_postfix_expression_named_refined_spine_tree refined =
      phase1_surface_postfix_expression_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [named_tree | primary projections].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_named_postfix_expression_refined_tail_tree
        named_tree)
      as [named |] eqn:Hnamed; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_named_postfix_expression_refined_tail_tree_round_trip
        named_tree named Hnamed).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_postfix_expression_named_refined_tree
  (tree : ParseTree)
  : option Phase1SurfacePostfixExpressionNamedRefinedSpine :=
  match phase1_surface_normalize_postfix_expression_spine tree with
  | Some expression =>
      phase1_surface_normalize_postfix_expression_named_refined_spine expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_postfix_expression_named_refined_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_postfix_expression_named_refined_tree tree =
      Some refined ->
    phase1_surface_postfix_expression_named_refined_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_postfix_expression_named_refined_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_postfix_expression_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity (phase1_surface_postfix_expression_spine_tree expression).
  - eapply
      phase1_surface_normalize_postfix_expression_named_refined_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_postfix_expression_spine_round_trip.
    exact Hexpression.
Qed.
