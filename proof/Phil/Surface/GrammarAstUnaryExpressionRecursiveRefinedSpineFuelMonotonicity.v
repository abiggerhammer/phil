From Stdlib Require Import Lia.

From Phil.Surface Require Import
  GrammarAstUnaryExpressionRecursiveRefinedSpine.

(*
  Fuel monotonicity for the recursive unary-expression refinement. Successful
  normalization is stable under increasing the explicit recursion fuel.
  This is support for PHIL-SURFACE-GRAMMAR-CORR-001 multiplicative-expression
  shared-fuel totality.
*)

Lemma
  phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel_monotone :
  forall fuel larger expression refined,
    fuel <= larger ->
    phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel
      larger expression = Some refined.
Proof.
  induction fuel as [|fuel IH];
    intros larger expression refined Hle Hnormalize.
  - cbn in Hnormalize.
    discriminate Hnormalize.
  - destruct larger as [|larger].
    + lia.
    + assert (Hle' : fuel <= larger) by lia.
      destruct expression as [operand_tree | postfix].
      * cbn in Hnormalize |- *.
        destruct
          (phase1_surface_normalize_unary_expression_postfix_refined_tree
            operand_tree)
          as [operand |] eqn:Hoperand;
          cbn in Hnormalize |- *; try discriminate Hnormalize.
        destruct
          (phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel
            fuel operand)
          as [refined_operand |] eqn:Hrecursive;
          try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        rewrite
          (IH larger operand refined_operand Hle' Hrecursive).
        reflexivity.
      * cbn in Hnormalize |- *.
        inversion Hnormalize; subst refined.
        reflexivity.
Qed.

Lemma
  phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_unary_expression_postfix_refined_tree tree)
    as [expression |] eqn:Hexpression;
    try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_unary_expression_recursive_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.
