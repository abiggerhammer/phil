From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstMultiplicativeExpressionSpine
  GrammarAstUnaryExpressionRecursiveRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the unary_expression payload of one repeated multiplicative suffix:

    ( "*" | "/" | "%" ), unary_expression

  The operator keeps the existing exact multiplicative-operator carrier. The
  right operand now carries the completed recursive unary-expression refinement
  instead of an opaque certified ParseTree.

  Normalization is fuel-bounded only because recursive unary normalization is.
  Successful normalization reconstructs the exact original suffix carrier and
  therefore the exact certified suffix parse tree.

  Structural correspondence only. This does not yet lift the refinement over
  suffix lists or the whole multiplicative expression, prove a total fuel bound,
  add evaluation semantics, change Grammar-v1, alter Haskell, or make broader
  production-parser claims. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Record Phase1SurfaceMultiplicativeSuffixRefinedSpine : Type := {
  phase1_multiplicative_suffix_refined_spine_operator :
    Phase1SurfaceMultiplicativeOperatorSpine;
  phase1_multiplicative_suffix_refined_spine_right :
    Phase1SurfaceUnaryExpressionRecursiveRefinedSpine
}.

Definition phase1_surface_multiplicative_suffix_refined_spine_base
  (suffix : Phase1SurfaceMultiplicativeSuffixRefinedSpine)
  : Phase1SurfaceMultiplicativeSuffixSpine :=
  {| phase1_multiplicative_suffix_spine_operator :=
       phase1_multiplicative_suffix_refined_spine_operator suffix;
     phase1_multiplicative_suffix_spine_right :=
       phase1_surface_unary_expression_recursive_refined_spine_tree
         (phase1_multiplicative_suffix_refined_spine_right suffix) |}.

Definition phase1_surface_multiplicative_suffix_refined_spine_tree
  (suffix : Phase1SurfaceMultiplicativeSuffixRefinedSpine)
  : ParseTree :=
  phase1_surface_multiplicative_suffix_spine_tree
    (phase1_surface_multiplicative_suffix_refined_spine_base suffix).

Definition phase1_surface_normalize_multiplicative_suffix_refined_spine_fuel
  (fuel : nat)
  (suffix : Phase1SurfaceMultiplicativeSuffixSpine)
  : option Phase1SurfaceMultiplicativeSuffixRefinedSpine :=
  match
    phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
      fuel
      (phase1_multiplicative_suffix_spine_right suffix)
  with
  | Some right =>
      Some
        {| phase1_multiplicative_suffix_refined_spine_operator :=
             phase1_multiplicative_suffix_spine_operator suffix;
           phase1_multiplicative_suffix_refined_spine_right := right |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_multiplicative_suffix_refined_spine_fuel_round_trip :
  forall fuel suffix refined,
    phase1_surface_normalize_multiplicative_suffix_refined_spine_fuel
      fuel suffix = Some refined ->
    phase1_surface_multiplicative_suffix_refined_spine_base refined = suffix.
Proof.
  intros fuel suffix refined Hnormalize.
  unfold phase1_surface_normalize_multiplicative_suffix_refined_spine_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
      fuel
      (phase1_multiplicative_suffix_spine_right suffix))
    as [right |] eqn:Hright; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_multiplicative_suffix_refined_spine_base.
  cbn.
  rewrite
    (phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_round_trip
      fuel
      (phase1_multiplicative_suffix_spine_right suffix)
      right
      Hright).
  destruct suffix.
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_multiplicative_suffix_refined_spine_fuel_tree_round_trip :
  forall fuel suffix refined,
    phase1_surface_normalize_multiplicative_suffix_refined_spine_fuel
      fuel suffix = Some refined ->
    phase1_surface_multiplicative_suffix_refined_spine_tree refined =
      phase1_surface_multiplicative_suffix_spine_tree suffix.
Proof.
  intros fuel suffix refined Hnormalize.
  unfold phase1_surface_multiplicative_suffix_refined_spine_tree.
  rewrite
    (phase1_surface_normalize_multiplicative_suffix_refined_spine_fuel_round_trip
      fuel suffix refined Hnormalize).
  reflexivity.
Qed.
