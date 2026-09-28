From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPostfixExpressionRefinedSpine
  GrammarAstUnaryExpressionSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the retained postfix_expression payload beneath the unary_expression
  shell:

    unary_expression =
        "-", unary_expression
      | postfix_expression
      ;

  The postfix branch now carries the fully refined postfix-expression spine
  completed through the primary-expression integer slice. The recursive
  negation operand remains an exact certified unary_expression ParseTree for a
  dedicated successor refinement.

  This remains structural correspondence only. It does not add evaluation
  semantics, change Grammar-v1, close the recursive negation payload, refine
  multiplicative-expression operands, or make broader production-parser
  soundness/completeness claims. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Inductive Phase1SurfaceUnaryExpressionPostfixRefinedSpine : Type :=
| Phase1SurfaceUnaryExpressionNegateRetained
    (operand : ParseTree)
| Phase1SurfaceUnaryExpressionPostfixRefined
    (postfix : Phase1SurfacePostfixExpressionRefinedSpine).

Definition phase1_surface_unary_expression_postfix_refined_spine_tree
  (expression : Phase1SurfaceUnaryExpressionPostfixRefinedSpine) : ParseTree :=
  match expression with
  | Phase1SurfaceUnaryExpressionNegateRetained operand =>
      phase1_surface_unary_expression_spine_tree
        (Phase1SurfaceUnaryExpressionNegate operand)
  | Phase1SurfaceUnaryExpressionPostfixRefined postfix =>
      phase1_surface_unary_expression_spine_tree
        (Phase1SurfaceUnaryExpressionPostfix
          (phase1_surface_postfix_expression_refined_spine_tree postfix))
  end.

Definition phase1_surface_normalize_unary_expression_postfix_refined_spine
  (expression : Phase1SurfaceUnaryExpressionSpine)
  : option Phase1SurfaceUnaryExpressionPostfixRefinedSpine :=
  match expression with
  | Phase1SurfaceUnaryExpressionNegate operand =>
      Some (Phase1SurfaceUnaryExpressionNegateRetained operand)
  | Phase1SurfaceUnaryExpressionPostfix postfix_tree =>
      match phase1_surface_normalize_postfix_expression_refined_tree postfix_tree with
      | Some postfix =>
          Some (Phase1SurfaceUnaryExpressionPostfixRefined postfix)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_unary_expression_postfix_refined_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_unary_expression_postfix_refined_spine expression =
      Some refined ->
    phase1_surface_unary_expression_postfix_refined_spine_tree refined =
      phase1_surface_unary_expression_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [operand | postfix_tree].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_postfix_expression_refined_tree postfix_tree)
      as [postfix |] eqn:Hpostfix; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_postfix_expression_refined_tree_round_trip
        postfix_tree postfix Hpostfix).
    reflexivity.
Qed.

Definition phase1_surface_normalize_unary_expression_postfix_refined_tree
  (tree : ParseTree)
  : option Phase1SurfaceUnaryExpressionPostfixRefinedSpine :=
  match phase1_surface_normalize_unary_expression_spine tree with
  | Some expression =>
      phase1_surface_normalize_unary_expression_postfix_refined_spine expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_unary_expression_postfix_refined_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_unary_expression_postfix_refined_tree tree =
      Some refined ->
    phase1_surface_unary_expression_postfix_refined_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_unary_expression_postfix_refined_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_unary_expression_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity (phase1_surface_unary_expression_spine_tree expression).
  - eapply
      phase1_surface_normalize_unary_expression_postfix_refined_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_unary_expression_spine_round_trip.
    exact Hexpression.
Qed.
