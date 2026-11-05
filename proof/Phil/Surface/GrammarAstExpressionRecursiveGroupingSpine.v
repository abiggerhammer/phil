From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstFallbackBaseChoiceSpine
  GrammarAstExpressionFallbackBaseChoiceSpine
  GrammarAstExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstBaseExpressionRecursiveGroupingSpine
  GrammarAstFallbackRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Consume the recursive grouping base carrier in the ordinary expression's
  main base and the new fallback carrier in its optional fallback. Thus a
  reject fallback also contains a typed base expression. Both fields replace
  their predecessor representations instead of storing a second view.

  The existing shell decoder supplies the exact optional "or" structure.
  Failure targets and command bodies remain exact ParseTree boundaries, as do
  nested fallback payloads in the separate generic recursive grouping carrier.
  This slice does not change semantics or bind the production Haskell AST.
*)

Definition phase1_surface_normalize_optional_fallback_recursive_grouping_spine
  (previous : option Phase1SurfaceFallbackBaseChoiceSpine)
  : option (option Phase1SurfaceFallbackRecursiveGroupingSpine) :=
  match previous with
  | None => Some None
  | Some fallback =>
      match phase1_surface_normalize_fallback_recursive_grouping_spine fallback
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_fallback_recursive_grouping_spine_round_trip :
  forall previous refined,
    phase1_surface_normalize_optional_fallback_recursive_grouping_spine
      previous = Some refined ->
    option_map phase1_surface_fallback_recursive_grouping_spine_base refined =
      previous.
Proof.
  intros [fallback |] refined Hnormalize.
  - cbn [phase1_surface_normalize_optional_fallback_recursive_grouping_spine]
      in Hnormalize.
    destruct
      (phase1_surface_normalize_fallback_recursive_grouping_spine fallback)
      as [actual |] eqn:Hfallback; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn [option_map].
    rewrite
      (phase1_surface_normalize_fallback_recursive_grouping_spine_round_trip
        fallback actual Hfallback).
    reflexivity.
  - inversion Hnormalize; reflexivity.
Qed.

Record Phase1SurfaceExpressionRecursiveGroupingSpine : Type := {
  phase1_expression_recursive_grouping_spine_base :
    Phase1SurfaceBaseExpressionRecursiveGroupingSpine;
  phase1_expression_recursive_grouping_spine_fallback :
    option Phase1SurfaceFallbackRecursiveGroupingSpine
}.

Definition phase1_surface_expression_recursive_grouping_spine_base
  (expression : Phase1SurfaceExpressionRecursiveGroupingSpine)
  : Phase1SurfaceExpressionFallbackBaseChoiceSpine :=
  {| phase1_expression_fallback_base_choice_spine_base :=
       phase1_surface_base_expression_recursive_grouping_spine_base
         (phase1_expression_recursive_grouping_spine_base expression);
     phase1_expression_fallback_base_choice_spine_fallback :=
       option_map phase1_surface_fallback_recursive_grouping_spine_base
         (phase1_expression_recursive_grouping_spine_fallback expression) |}.

Definition phase1_surface_expression_recursive_grouping_spine_tree
  (expression : Phase1SurfaceExpressionRecursiveGroupingSpine) : ParseTree :=
  phase1_surface_expression_fallback_base_choice_spine_tree
    (phase1_surface_expression_recursive_grouping_spine_base expression).

Definition phase1_surface_normalize_expression_recursive_grouping_spine
  (previous : Phase1SurfaceExpressionFallbackBaseChoiceSpine)
  : option Phase1SurfaceExpressionRecursiveGroupingSpine :=
  match
    phase1_surface_normalize_base_expression_recursive_grouping_spine
      (phase1_expression_fallback_base_choice_spine_base previous),
    phase1_surface_normalize_optional_fallback_recursive_grouping_spine
      (phase1_expression_fallback_base_choice_spine_fallback previous)
  with
  | Some refined_base, Some refined_fallback =>
      Some
        {| phase1_expression_recursive_grouping_spine_base := refined_base;
           phase1_expression_recursive_grouping_spine_fallback :=
             refined_fallback |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_expression_recursive_grouping_spine_round_trip :
  forall previous refined,
    phase1_surface_normalize_expression_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_expression_recursive_grouping_spine_base refined = previous.
Proof.
  intros [base fallback] refined Hnormalize.
  unfold phase1_surface_normalize_expression_recursive_grouping_spine
    in Hnormalize.
  cbn [phase1_expression_fallback_base_choice_spine_base
    phase1_expression_fallback_base_choice_spine_fallback] in Hnormalize.
  destruct
    (phase1_surface_normalize_base_expression_recursive_grouping_spine base)
    as [actual_base |] eqn:Hbase; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_optional_fallback_recursive_grouping_spine fallback)
    as [actual_fallback |] eqn:Hfallback; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_expression_recursive_grouping_spine_base.
  cbn [phase1_expression_recursive_grouping_spine_base
    phase1_expression_recursive_grouping_spine_fallback].
  rewrite
    (phase1_surface_normalize_base_expression_recursive_grouping_spine_round_trip
      base actual_base Hbase),
    (phase1_surface_normalize_optional_fallback_recursive_grouping_spine_round_trip
      fallback actual_fallback Hfallback).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_expression_recursive_grouping_spine_tree_round_trip :
  forall previous refined,
    phase1_surface_normalize_expression_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_expression_recursive_grouping_spine_tree refined =
      phase1_surface_expression_fallback_base_choice_spine_tree previous.
Proof.
  intros previous refined Hnormalize.
  unfold phase1_surface_expression_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_expression_recursive_grouping_spine_round_trip
      previous refined Hnormalize).
  reflexivity.
Qed.

Definition phase1_surface_normalize_expression_recursive_grouping_tree
  (tree : ParseTree) : option Phase1SurfaceExpressionRecursiveGroupingSpine :=
  match phase1_surface_normalize_expression_fallback_base_choice_tree tree with
  | Some previous =>
      phase1_surface_normalize_expression_recursive_grouping_spine previous
  | None => None
  end.

Theorem phase1_surface_normalize_expression_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_expression_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_expression_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_expression_recursive_grouping_tree in Hnormalize.
  destruct (phase1_surface_normalize_expression_fallback_base_choice_tree tree)
    as [previous |] eqn:Hprevious; try discriminate Hnormalize.
  transitivity (phase1_surface_expression_fallback_base_choice_spine_tree previous).
  - eapply
      phase1_surface_normalize_expression_recursive_grouping_spine_tree_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_expression_fallback_base_choice_tree_round_trip.
    exact Hprevious.
Qed.

Definition phase1_surface_refine_expression_recursive_grouping
  (previous : Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine)
  : option Phase1SurfaceExpressionRecursiveGroupingSpine :=
  phase1_surface_normalize_expression_recursive_grouping_tree
    (phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
      previous).

Theorem phase1_surface_refine_expression_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_expression_recursive_grouping previous = Some refined ->
    phase1_surface_expression_recursive_grouping_spine_tree refined =
      phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
        previous.
Proof.
  intros previous refined Hnormalize.
  exact
    (phase1_surface_normalize_expression_recursive_grouping_tree_round_trip
      _ refined Hnormalize).
Qed.
