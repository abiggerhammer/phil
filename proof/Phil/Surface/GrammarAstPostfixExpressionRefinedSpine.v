From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPostfixExpressionNamedRefinedSpine
  GrammarAstPrimaryExpressionIntegerSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Close the retained primary_expression payload beneath the refined
  postfix_expression shell.

  The named branch already carries the refined named-postfix representation.
  The primary branch can now consume the fully refined primary_expression
  carrier completed through the integer-literal slice, while preserving the
  already-normalized projection-name spine.

  This remains structural correspondence only. It does not add numeric
  semantics, change Grammar-v1, refine unrelated expression layers, or make
  broader production-parser claims. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Inductive Phase1SurfacePostfixExpressionRefinedSpine : Type :=
| Phase1SurfacePostfixExpressionNamedFullyRefined
    (named : Phase1SurfaceNamedPostfixExpressionRefinedTailSpine)
| Phase1SurfacePostfixExpressionPrimaryRefined
    (primary : Phase1SurfacePrimaryExpressionIntegerSpine)
    (projections : list string).

Definition phase1_surface_postfix_expression_refined_spine_tree
  (expression : Phase1SurfacePostfixExpressionRefinedSpine) : ParseTree :=
  match expression with
  | Phase1SurfacePostfixExpressionNamedFullyRefined named =>
      phase1_surface_postfix_expression_named_refined_spine_tree
        (Phase1SurfacePostfixExpressionNamedRefined named)
  | Phase1SurfacePostfixExpressionPrimaryRefined primary projections =>
      phase1_surface_postfix_expression_named_refined_spine_tree
        (Phase1SurfacePostfixExpressionPrimaryRetained
          (phase1_surface_primary_expression_integer_spine_tree primary)
          projections)
  end.

Definition phase1_surface_normalize_postfix_expression_refined_spine
  (expression : Phase1SurfacePostfixExpressionNamedRefinedSpine)
  : option Phase1SurfacePostfixExpressionRefinedSpine :=
  match expression with
  | Phase1SurfacePostfixExpressionNamedRefined named =>
      Some (Phase1SurfacePostfixExpressionNamedFullyRefined named)
  | Phase1SurfacePostfixExpressionPrimaryRetained primary_tree projections =>
      match phase1_surface_normalize_primary_expression_integer_tree primary_tree with
      | Some primary =>
          Some
            (Phase1SurfacePostfixExpressionPrimaryRefined
              primary projections)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_postfix_expression_refined_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_postfix_expression_refined_spine expression =
      Some refined ->
    phase1_surface_postfix_expression_refined_spine_tree refined =
      phase1_surface_postfix_expression_named_refined_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [named | primary_tree projections].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_primary_expression_integer_tree primary_tree)
      as [primary |] eqn:Hprimary;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_primary_expression_integer_tree_round_trip
        primary_tree primary Hprimary).
    reflexivity.
Qed.

Definition phase1_surface_normalize_postfix_expression_refined_tree
  (tree : ParseTree)
  : option Phase1SurfacePostfixExpressionRefinedSpine :=
  match phase1_surface_normalize_postfix_expression_named_refined_tree tree with
  | Some expression =>
      phase1_surface_normalize_postfix_expression_refined_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_postfix_expression_refined_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_postfix_expression_refined_tree tree =
      Some refined ->
    phase1_surface_postfix_expression_refined_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_postfix_expression_refined_tree in Hnormalize.
  destruct
    (phase1_surface_normalize_postfix_expression_named_refined_tree tree)
    as [expression |] eqn:Hexpression;
    try discriminate Hnormalize.
  transitivity
    (phase1_surface_postfix_expression_named_refined_spine_tree expression).
  - eapply
      phase1_surface_normalize_postfix_expression_refined_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_postfix_expression_named_refined_tree_round_trip.
    exact Hexpression.
Qed.
