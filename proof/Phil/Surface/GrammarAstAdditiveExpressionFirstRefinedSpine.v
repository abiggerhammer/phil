From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstAdditiveExpressionSpine
  GrammarAstMultiplicativeExpressionRefinedSpine.

(*
  Refine the first multiplicative_expression operand beneath the additive shell:

    additive_expression =
      multiplicative_expression,
      { ( "+" | "-" ), multiplicative_expression } ;

  The leading operand now carries the completed multiplicative-expression
  refinement. Repeated additive suffix operands remain exact certified
  ParseTrees for dedicated successor refinement.

  Normalization is fuel-bounded only because the completed multiplicative
  carrier shares recursion fuel across its recursive unary-expression
  descendants. Successful normalization reconstructs the exact prior additive
  carrier and exact certified parse tree.

  Structural correspondence only. This does not refine repeated additive
  suffix operands, add evaluation semantics, change Grammar-v1, alter Haskell,
  or make broader production-parser soundness/completeness claims. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Record Phase1SurfaceAdditiveExpressionFirstRefinedSpine : Type := {
  phase1_additive_expression_first_refined_spine_first :
    Phase1SurfaceMultiplicativeExpressionRefinedSpine;
  phase1_additive_expression_first_refined_spine_rest :
    list Phase1SurfaceAdditiveSuffixSpine
}.

Definition phase1_surface_additive_expression_first_refined_spine_tree
  (expression : Phase1SurfaceAdditiveExpressionFirstRefinedSpine)
  : ParseTree :=
  phase1_surface_additive_expression_spine_tree
    {| phase1_additive_expression_spine_first :=
         phase1_surface_multiplicative_expression_refined_spine_tree
           (phase1_additive_expression_first_refined_spine_first expression);
       phase1_additive_expression_spine_rest :=
         phase1_additive_expression_first_refined_spine_rest expression |}.

Definition
  phase1_surface_normalize_additive_expression_first_refined_spine_fuel
  (fuel : nat)
  (expression : Phase1SurfaceAdditiveExpressionSpine)
  : option Phase1SurfaceAdditiveExpressionFirstRefinedSpine :=
  match
    phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
      fuel
      (phase1_additive_expression_spine_first expression)
  with
  | Some first =>
      Some
        {| phase1_additive_expression_first_refined_spine_first := first;
           phase1_additive_expression_first_refined_spine_rest :=
             phase1_additive_expression_spine_rest expression |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_additive_expression_first_refined_spine_fuel_round_trip :
  forall fuel expression refined,
    phase1_surface_normalize_additive_expression_first_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_additive_expression_first_refined_spine_tree refined =
      phase1_surface_additive_expression_spine_tree expression.
Proof.
  intros fuel expression refined Hnormalize.
  unfold
    phase1_surface_normalize_additive_expression_first_refined_spine_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
      fuel
      (phase1_additive_expression_spine_first expression))
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_additive_expression_first_refined_spine_tree.
  cbn.
  rewrite
    (phase1_surface_normalize_multiplicative_expression_refined_tree_fuel_round_trip
      fuel
      (phase1_additive_expression_spine_first expression)
      first
      Hfirst).
  destruct expression.
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_additive_expression_first_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceAdditiveExpressionFirstRefinedSpine :=
  match phase1_surface_normalize_additive_expression_spine tree with
  | Some expression =>
      phase1_surface_normalize_additive_expression_first_refined_spine_fuel
        fuel expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_additive_expression_first_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_additive_expression_first_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_additive_expression_first_refined_spine_tree refined =
      tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_additive_expression_first_refined_tree_fuel
    in Hnormalize.
  destruct (phase1_surface_normalize_additive_expression_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity (phase1_surface_additive_expression_spine_tree expression).
  - eapply
      phase1_surface_normalize_additive_expression_first_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_additive_expression_spine_round_trip.
    exact Hexpression.
Qed.
