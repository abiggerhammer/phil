From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstUnaryExpressionPostfixRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the recursive unary_expression negation payload retained by the
  postfix-refined unary spine. Postfix leaves reuse the completed
  postfix-expression refinement, while negation nodes carry recursively
  refined unary expressions instead of opaque ParseTree payloads.

  Normalization is fuel-bounded so termination is explicit. Successful
  normalization reconstructs the exact certified parse tree. A
  derivation-driven sufficient-fuel theorem is left to a focused successor.

  Structural correspondence only. This does not add evaluation semantics,
  change Grammar-v1, refine multiplicative-expression operands, establish a
  total fuel bound here, alter Haskell, or make broader parser claims.
  Continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Inductive Phase1SurfaceUnaryExpressionRecursiveRefinedSpine : Type :=
| Phase1SurfaceUnaryExpressionNegateRecursiveRefined
    (operand : Phase1SurfaceUnaryExpressionRecursiveRefinedSpine)
| Phase1SurfaceUnaryExpressionPostfixRecursiveRefined
    (postfix : Phase1SurfacePostfixExpressionRefinedSpine).

Fixpoint phase1_surface_unary_expression_recursive_refined_spine_tree
  (expression : Phase1SurfaceUnaryExpressionRecursiveRefinedSpine)
  : ParseTree :=
  match expression with
  | Phase1SurfaceUnaryExpressionNegateRecursiveRefined operand =>
      phase1_surface_unary_expression_postfix_refined_spine_tree
        (Phase1SurfaceUnaryExpressionNegateRetained
          (phase1_surface_unary_expression_recursive_refined_spine_tree
            operand))
  | Phase1SurfaceUnaryExpressionPostfixRecursiveRefined postfix =>
      phase1_surface_unary_expression_postfix_refined_spine_tree
        (Phase1SurfaceUnaryExpressionPostfixRefined postfix)
  end.

Fixpoint phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel
  (fuel : nat)
  (expression : Phase1SurfaceUnaryExpressionPostfixRefinedSpine)
  : option Phase1SurfaceUnaryExpressionRecursiveRefinedSpine :=
  match fuel with
  | O => None
  | S fuel' =>
      match expression with
      | Phase1SurfaceUnaryExpressionNegateRetained operand_tree =>
          match
            phase1_surface_normalize_unary_expression_postfix_refined_tree
              operand_tree
          with
          | Some operand =>
              match
                phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel
                  fuel' operand
              with
              | Some refined_operand =>
                  Some
                    (Phase1SurfaceUnaryExpressionNegateRecursiveRefined
                      refined_operand)
              | None => None
              end
          | None => None
          end
      | Phase1SurfaceUnaryExpressionPostfixRefined postfix =>
          Some
            (Phase1SurfaceUnaryExpressionPostfixRecursiveRefined postfix)
      end
  end.

Theorem
  phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel_round_trip :
  forall fuel expression refined,
    phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_unary_expression_recursive_refined_spine_tree refined =
      phase1_surface_unary_expression_postfix_refined_spine_tree expression.
Proof.
  induction fuel as [|fuel IH]; intros expression refined Hnormalize.
  - discriminate Hnormalize.
  - destruct expression as [operand_tree | postfix].
    + cbn in Hnormalize.
      destruct
        (phase1_surface_normalize_unary_expression_postfix_refined_tree
          operand_tree)
        as [operand |] eqn:Hoperand; try discriminate Hnormalize.
      destruct
        (phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel
          fuel operand)
        as [refined_operand |] eqn:Hrecursive;
        try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (IH operand refined_operand Hrecursive).
      rewrite
        (phase1_surface_normalize_unary_expression_postfix_refined_tree_round_trip
          operand_tree operand Hoperand).
      reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
Qed.

Definition phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceUnaryExpressionRecursiveRefinedSpine :=
  match phase1_surface_normalize_unary_expression_postfix_refined_tree tree with
  | Some expression =>
      phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel
        fuel expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_unary_expression_recursive_refined_spine_tree refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_unary_expression_postfix_refined_tree tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity
    (phase1_surface_unary_expression_postfix_refined_spine_tree expression).
  - eapply
      phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_unary_expression_postfix_refined_tree_round_trip.
    exact Hexpression.
Qed.
