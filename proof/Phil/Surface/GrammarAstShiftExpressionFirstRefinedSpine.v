From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstShiftExpressionSpine
  GrammarAstAdditiveExpressionRefinedSpine.

(*
  Refine the first additive_expression operand beneath the shift shell:

    shift_expression =
      additive_expression,
      { ( "<<" | ">>" ), additive_expression } ;

  The leading operand now carries the completed additive-expression refinement.
  Repeated shift suffix operands remain exact certified ParseTrees for dedicated
  successor refinement.

  Normalization is fuel-bounded only because the completed additive carrier
  shares recursion fuel across its refined descendants. Successful
  normalization reconstructs the exact prior shift carrier and exact certified
  parse tree.

  Structural correspondence only. This does not refine repeated shift suffix
  operands, add evaluation semantics, change Grammar-v1, alter Haskell, or make
  broader production-parser soundness/completeness claims. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Record Phase1SurfaceShiftExpressionFirstRefinedSpine : Type := {
  phase1_shift_expression_first_refined_spine_first :
    Phase1SurfaceAdditiveExpressionRefinedSpine;
  phase1_shift_expression_first_refined_spine_rest :
    list Phase1SurfaceShiftSuffixSpine
}.

Definition phase1_surface_shift_expression_first_refined_spine_tree
  (expression : Phase1SurfaceShiftExpressionFirstRefinedSpine)
  : ParseTree :=
  phase1_surface_shift_expression_spine_tree
    {| phase1_shift_expression_spine_first :=
         phase1_surface_additive_expression_refined_spine_tree
           (phase1_shift_expression_first_refined_spine_first expression);
       phase1_shift_expression_spine_rest :=
         phase1_shift_expression_first_refined_spine_rest expression |}.

Definition
  phase1_surface_normalize_shift_expression_first_refined_spine_fuel
  (fuel : nat)
  (expression : Phase1SurfaceShiftExpressionSpine)
  : option Phase1SurfaceShiftExpressionFirstRefinedSpine :=
  match
    phase1_surface_normalize_additive_expression_refined_tree_fuel
      fuel
      (phase1_shift_expression_spine_first expression)
  with
  | Some first =>
      Some
        {| phase1_shift_expression_first_refined_spine_first := first;
           phase1_shift_expression_first_refined_spine_rest :=
             phase1_shift_expression_spine_rest expression |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_shift_expression_first_refined_spine_fuel_round_trip :
  forall fuel expression refined,
    phase1_surface_normalize_shift_expression_first_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_shift_expression_first_refined_spine_tree refined =
      phase1_surface_shift_expression_spine_tree expression.
Proof.
  intros fuel expression refined Hnormalize.
  unfold
    phase1_surface_normalize_shift_expression_first_refined_spine_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_additive_expression_refined_tree_fuel
      fuel
      (phase1_shift_expression_spine_first expression))
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_shift_expression_first_refined_spine_tree.
  cbn.
  rewrite
    (phase1_surface_normalize_additive_expression_refined_tree_fuel_round_trip
      fuel
      (phase1_shift_expression_spine_first expression)
      first
      Hfirst).
  destruct expression.
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_shift_expression_first_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceShiftExpressionFirstRefinedSpine :=
  match phase1_surface_normalize_shift_expression_spine tree with
  | Some expression =>
      phase1_surface_normalize_shift_expression_first_refined_spine_fuel
        fuel expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_shift_expression_first_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_shift_expression_first_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_shift_expression_first_refined_spine_tree refined =
      tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_shift_expression_first_refined_tree_fuel
    in Hnormalize.
  destruct (phase1_surface_normalize_shift_expression_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity (phase1_surface_shift_expression_spine_tree expression).
  - eapply
      phase1_surface_normalize_shift_expression_first_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_shift_expression_spine_round_trip.
    exact Hexpression.
Qed.
