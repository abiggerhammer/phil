From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstAdditiveExpressionSpine
  GrammarAstMultiplicativeExpressionRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the multiplicative_expression payload of one repeated additive suffix:

    ( "+" | "-" ), multiplicative_expression

  The operator keeps the existing exact additive-operator carrier. The right
  operand now carries the completed multiplicative-expression refinement
  instead of an opaque certified ParseTree.

  Normalization is fuel-bounded only because multiplicative-expression
  normalization shares recursion fuel with recursive unary descendants.
  Successful normalization reconstructs the exact original suffix carrier and
  therefore the exact certified suffix parse tree.

  Structural correspondence only. This does not yet lift the refinement over
  suffix lists or the whole additive expression, prove a total shared fuel
  bound, add evaluation semantics, change Grammar-v1, alter Haskell, or make
  broader production-parser soundness/completeness claims. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Record Phase1SurfaceAdditiveSuffixRefinedSpine : Type := {
  phase1_additive_suffix_refined_spine_operator :
    Phase1SurfaceAdditiveOperatorSpine;
  phase1_additive_suffix_refined_spine_right :
    Phase1SurfaceMultiplicativeExpressionRefinedSpine
}.

Definition phase1_surface_additive_suffix_refined_spine_base
  (suffix : Phase1SurfaceAdditiveSuffixRefinedSpine)
  : Phase1SurfaceAdditiveSuffixSpine :=
  {| phase1_additive_suffix_spine_operator :=
       phase1_additive_suffix_refined_spine_operator suffix;
     phase1_additive_suffix_spine_right :=
       phase1_surface_multiplicative_expression_refined_spine_tree
         (phase1_additive_suffix_refined_spine_right suffix) |}.

Definition phase1_surface_additive_suffix_refined_spine_tree
  (suffix : Phase1SurfaceAdditiveSuffixRefinedSpine)
  : ParseTree :=
  phase1_surface_additive_suffix_spine_tree
    (phase1_surface_additive_suffix_refined_spine_base suffix).

Definition phase1_surface_normalize_additive_suffix_refined_spine_fuel
  (fuel : nat)
  (suffix : Phase1SurfaceAdditiveSuffixSpine)
  : option Phase1SurfaceAdditiveSuffixRefinedSpine :=
  match
    phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
      fuel
      (phase1_additive_suffix_spine_right suffix)
  with
  | Some right =>
      Some
        {| phase1_additive_suffix_refined_spine_operator :=
             phase1_additive_suffix_spine_operator suffix;
           phase1_additive_suffix_refined_spine_right := right |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_additive_suffix_refined_spine_fuel_round_trip :
  forall fuel suffix refined,
    phase1_surface_normalize_additive_suffix_refined_spine_fuel
      fuel suffix = Some refined ->
    phase1_surface_additive_suffix_refined_spine_base refined = suffix.
Proof.
  intros fuel suffix refined Hnormalize.
  unfold phase1_surface_normalize_additive_suffix_refined_spine_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
      fuel
      (phase1_additive_suffix_spine_right suffix))
    as [right |] eqn:Hright; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_additive_suffix_refined_spine_base.
  cbn.
  rewrite
    (phase1_surface_normalize_multiplicative_expression_refined_tree_fuel_round_trip
      fuel
      (phase1_additive_suffix_spine_right suffix)
      right
      Hright).
  destruct suffix.
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_additive_suffix_refined_spine_fuel_tree_round_trip :
  forall fuel suffix refined,
    phase1_surface_normalize_additive_suffix_refined_spine_fuel
      fuel suffix = Some refined ->
    phase1_surface_additive_suffix_refined_spine_tree refined =
      phase1_surface_additive_suffix_spine_tree suffix.
Proof.
  intros fuel suffix refined Hnormalize.
  unfold phase1_surface_additive_suffix_refined_spine_tree.
  rewrite
    (phase1_surface_normalize_additive_suffix_refined_spine_fuel_round_trip
      fuel suffix refined Hnormalize).
  reflexivity.
Qed.
