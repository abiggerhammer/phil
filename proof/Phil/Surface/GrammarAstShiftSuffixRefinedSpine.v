From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstShiftExpressionSpine
  GrammarAstAdditiveExpressionRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the additive_expression payload of one repeated shift suffix:

    ( "<<" | ">>" ), additive_expression

  The operator keeps the existing exact shift-operator carrier. The right
  operand now carries the completed additive-expression refinement instead of
  an opaque certified ParseTree.

  Normalization is fuel-bounded only because additive-expression normalization
  shares recursion fuel with its refined descendants. Successful normalization
  reconstructs the exact original suffix carrier and therefore the exact
  certified suffix parse tree.

  Structural correspondence only. This does not yet lift the refinement over
  suffix lists or the whole shift expression, prove a total shared fuel bound,
  add evaluation semantics, change Grammar-v1, alter Haskell, refine enclosing
  base/relation layers, or make broader production-parser soundness/completeness
  claims. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Record Phase1SurfaceShiftSuffixRefinedSpine : Type := {
  phase1_shift_suffix_refined_spine_operator :
    Phase1SurfaceShiftOperatorSpine;
  phase1_shift_suffix_refined_spine_right :
    Phase1SurfaceAdditiveExpressionRefinedSpine
}.

Definition phase1_surface_shift_suffix_refined_spine_base
  (suffix : Phase1SurfaceShiftSuffixRefinedSpine)
  : Phase1SurfaceShiftSuffixSpine :=
  {| phase1_shift_suffix_spine_operator :=
       phase1_shift_suffix_refined_spine_operator suffix;
     phase1_shift_suffix_spine_right :=
       phase1_surface_additive_expression_refined_spine_tree
         (phase1_shift_suffix_refined_spine_right suffix) |}.

Definition phase1_surface_shift_suffix_refined_spine_tree
  (suffix : Phase1SurfaceShiftSuffixRefinedSpine)
  : ParseTree :=
  phase1_surface_shift_suffix_spine_tree
    (phase1_surface_shift_suffix_refined_spine_base suffix).

Definition phase1_surface_normalize_shift_suffix_refined_spine_fuel
  (fuel : nat)
  (suffix : Phase1SurfaceShiftSuffixSpine)
  : option Phase1SurfaceShiftSuffixRefinedSpine :=
  match
    phase1_surface_normalize_additive_expression_refined_tree_fuel
      fuel
      (phase1_shift_suffix_spine_right suffix)
  with
  | Some right =>
      Some
        {| phase1_shift_suffix_refined_spine_operator :=
             phase1_shift_suffix_spine_operator suffix;
           phase1_shift_suffix_refined_spine_right := right |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_shift_suffix_refined_spine_fuel_round_trip :
  forall fuel suffix refined,
    phase1_surface_normalize_shift_suffix_refined_spine_fuel
      fuel suffix = Some refined ->
    phase1_surface_shift_suffix_refined_spine_base refined = suffix.
Proof.
  intros fuel suffix refined Hnormalize.
  unfold phase1_surface_normalize_shift_suffix_refined_spine_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_additive_expression_refined_tree_fuel
      fuel
      (phase1_shift_suffix_spine_right suffix))
    as [right |] eqn:Hright; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_shift_suffix_refined_spine_base.
  cbn.
  rewrite
    (phase1_surface_normalize_additive_expression_refined_tree_fuel_round_trip
      fuel
      (phase1_shift_suffix_spine_right suffix)
      right
      Hright).
  destruct suffix.
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_shift_suffix_refined_spine_fuel_tree_round_trip :
  forall fuel suffix refined,
    phase1_surface_normalize_shift_suffix_refined_spine_fuel
      fuel suffix = Some refined ->
    phase1_surface_shift_suffix_refined_spine_tree refined =
      phase1_surface_shift_suffix_spine_tree suffix.
Proof.
  intros fuel suffix refined Hnormalize.
  unfold phase1_surface_shift_suffix_refined_spine_tree.
  rewrite
    (phase1_surface_normalize_shift_suffix_refined_spine_fuel_round_trip
      fuel suffix refined Hnormalize).
  reflexivity.
Qed.
