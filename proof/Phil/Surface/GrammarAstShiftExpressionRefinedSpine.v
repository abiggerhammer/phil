From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstShiftExpressionFirstRefinedSpine
  GrammarAstShiftSuffixRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the completed shift-suffix refinement across the repeated suffix list
  and the whole shift-expression carrier:

    shift_expression =
      additive_expression,
      { ( "<<" | ">>" ), additive_expression } ;

  The leading additive_expression already uses the completed refined additive
  carrier. This slice replaces every remaining opaque additive-expression
  ParseTree in the repeated shift suffixes with the same refined carrier.

  Successful fuel-bounded normalization reconstructs the exact prior
  first-refined shift carrier and exact certified parse tree. Structural
  correspondence only: this does not prove a sufficiently large shared fuel
  exists, add evaluation semantics, change Grammar-v1, alter Haskell, refine
  enclosing base/relation layers, or claim broader production-parser
  soundness/completeness. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Fixpoint phase1_surface_normalize_shift_suffix_refined_spines_fuel
  (fuel : nat)
  (suffixes : list Phase1SurfaceShiftSuffixSpine)
  : option (list Phase1SurfaceShiftSuffixRefinedSpine) :=
  match suffixes with
  | [] => Some []
  | suffix :: rest =>
      match
        phase1_surface_normalize_shift_suffix_refined_spine_fuel
          fuel suffix,
        phase1_surface_normalize_shift_suffix_refined_spines_fuel
          fuel rest
      with
      | Some refined_suffix, Some refined_rest =>
          Some (refined_suffix :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_shift_suffix_refined_spines_fuel_round_trip :
  forall fuel suffixes refined,
    phase1_surface_normalize_shift_suffix_refined_spines_fuel
      fuel suffixes = Some refined ->
    map phase1_surface_shift_suffix_refined_spine_base refined = suffixes.
Proof.
  intros fuel suffixes.
  induction suffixes as [|suffix rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_shift_suffix_refined_spine_fuel fuel suffix)
      as [refined_suffix |] eqn:Hsuffix; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_shift_suffix_refined_spines_fuel fuel rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_shift_suffix_refined_spine_fuel_round_trip
        fuel suffix refined_suffix Hsuffix).
    f_equal.
    eapply IH.
    exact Hrest.
Qed.

Record Phase1SurfaceShiftExpressionRefinedSpine : Type := {
  phase1_shift_expression_refined_spine_first :
    Phase1SurfaceAdditiveExpressionRefinedSpine;
  phase1_shift_expression_refined_spine_rest :
    list Phase1SurfaceShiftSuffixRefinedSpine
}.

Definition phase1_surface_shift_expression_refined_spine_base
  (expression : Phase1SurfaceShiftExpressionRefinedSpine)
  : Phase1SurfaceShiftExpressionFirstRefinedSpine :=
  {| phase1_shift_expression_first_refined_spine_first :=
       phase1_shift_expression_refined_spine_first expression;
     phase1_shift_expression_first_refined_spine_rest :=
       map phase1_surface_shift_suffix_refined_spine_base
         (phase1_shift_expression_refined_spine_rest expression) |}.

Definition phase1_surface_shift_expression_refined_spine_tree
  (expression : Phase1SurfaceShiftExpressionRefinedSpine)
  : ParseTree :=
  phase1_surface_shift_expression_first_refined_spine_tree
    (phase1_surface_shift_expression_refined_spine_base expression).

Definition phase1_surface_normalize_shift_expression_refined_spine_fuel
  (fuel : nat)
  (expression : Phase1SurfaceShiftExpressionFirstRefinedSpine)
  : option Phase1SurfaceShiftExpressionRefinedSpine :=
  match
    phase1_surface_normalize_shift_suffix_refined_spines_fuel
      fuel
      (phase1_shift_expression_first_refined_spine_rest expression)
  with
  | Some rest =>
      Some
        {| phase1_shift_expression_refined_spine_first :=
             phase1_shift_expression_first_refined_spine_first expression;
           phase1_shift_expression_refined_spine_rest := rest |}
  | None => None
  end.

Theorem phase1_surface_normalize_shift_expression_refined_spine_fuel_round_trip :
  forall fuel expression refined,
    phase1_surface_normalize_shift_expression_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_shift_expression_refined_spine_base refined = expression.
Proof.
  intros fuel expression refined Hnormalize.
  unfold phase1_surface_normalize_shift_expression_refined_spine_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_shift_suffix_refined_spines_fuel
      fuel
      (phase1_shift_expression_first_refined_spine_rest expression))
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_shift_expression_refined_spine_base.
  cbn.
  rewrite
    (phase1_surface_normalize_shift_suffix_refined_spines_fuel_round_trip
      fuel
      (phase1_shift_expression_first_refined_spine_rest expression)
      refined_rest
      Hrest).
  destruct expression.
  reflexivity.
Qed.

Theorem phase1_surface_normalize_shift_expression_refined_spine_fuel_tree_round_trip :
  forall fuel expression refined,
    phase1_surface_normalize_shift_expression_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_shift_expression_refined_spine_tree refined =
      phase1_surface_shift_expression_first_refined_spine_tree expression.
Proof.
  intros fuel expression refined Hnormalize.
  unfold phase1_surface_shift_expression_refined_spine_tree.
  rewrite
    (phase1_surface_normalize_shift_expression_refined_spine_fuel_round_trip
      fuel expression refined Hnormalize).
  reflexivity.
Qed.

Definition phase1_surface_normalize_shift_expression_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceShiftExpressionRefinedSpine :=
  match
    phase1_surface_normalize_shift_expression_first_refined_tree_fuel
      fuel tree
  with
  | Some expression =>
      phase1_surface_normalize_shift_expression_refined_spine_fuel
        fuel expression
  | None => None
  end.

Theorem phase1_surface_normalize_shift_expression_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_shift_expression_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_shift_expression_refined_spine_tree refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold phase1_surface_normalize_shift_expression_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_shift_expression_first_refined_tree_fuel
      fuel tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity
    (phase1_surface_shift_expression_first_refined_spine_tree expression).
  - eapply
      phase1_surface_normalize_shift_expression_refined_spine_fuel_tree_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_shift_expression_first_refined_tree_fuel_round_trip.
    exact Hexpression.
Qed.
