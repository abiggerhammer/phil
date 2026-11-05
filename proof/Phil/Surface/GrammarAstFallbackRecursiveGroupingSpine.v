From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstBaseExpressionChoiceSpine
  GrammarAstFallbackBaseChoiceSpine
  GrammarAstBaseExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Replace the reject fallback's base-expression field with the recursive
  grouping base carrier. The fail branch retains its exact failure_target
  ParseTree. No predecessor value or duplicate tree is stored alongside the
  new reject payload.

  The command branch of the base carrier remains an exact ParseTree boundary.
  Fallbacks retained inside the generic recursive grouping expression carrier
  are unchanged. These are structural correspondence statements, without
  evaluation semantics or a production Haskell AST binding.
*)

Inductive Phase1SurfaceFallbackRecursiveGroupingSpine : Type :=
| Phase1FallbackGroupingFail (failure_target : ParseTree)
| Phase1FallbackGroupingReject
    (base : Phase1SurfaceBaseExpressionRecursiveGroupingSpine).

Definition phase1_surface_fallback_recursive_grouping_spine_base
  (fallback : Phase1SurfaceFallbackRecursiveGroupingSpine)
  : Phase1SurfaceFallbackBaseChoiceSpine :=
  match fallback with
  | Phase1FallbackGroupingFail failure_target =>
      Phase1FallbackBaseChoiceFail failure_target
  | Phase1FallbackGroupingReject base =>
      Phase1FallbackBaseChoiceReject
        (phase1_surface_base_expression_recursive_grouping_spine_base base)
  end.

Definition phase1_surface_fallback_recursive_grouping_spine_tree
  (fallback : Phase1SurfaceFallbackRecursiveGroupingSpine) : ParseTree :=
  phase1_surface_fallback_base_choice_spine_tree
    (phase1_surface_fallback_recursive_grouping_spine_base fallback).

Definition phase1_surface_normalize_fallback_recursive_grouping_spine
  (previous : Phase1SurfaceFallbackBaseChoiceSpine)
  : option Phase1SurfaceFallbackRecursiveGroupingSpine :=
  match previous with
  | Phase1FallbackBaseChoiceFail failure_target =>
      Some (Phase1FallbackGroupingFail failure_target)
  | Phase1FallbackBaseChoiceReject base =>
      match phase1_surface_normalize_base_expression_recursive_grouping_spine
        base with
      | Some refined => Some (Phase1FallbackGroupingReject refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_fallback_recursive_grouping_spine_round_trip :
  forall previous refined,
    phase1_surface_normalize_fallback_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_fallback_recursive_grouping_spine_base refined = previous.
Proof.
  intros [failure_target | base] refined Hnormalize.
  - inversion Hnormalize; reflexivity.
  - unfold phase1_surface_normalize_fallback_recursive_grouping_spine
      in Hnormalize.
    destruct
      (phase1_surface_normalize_base_expression_recursive_grouping_spine base)
      as [actual |] eqn:Hbase; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn [phase1_surface_fallback_recursive_grouping_spine_base].
    rewrite
      (phase1_surface_normalize_base_expression_recursive_grouping_spine_round_trip
        base actual Hbase).
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_fallback_recursive_grouping_spine_tree_round_trip :
  forall previous refined,
    phase1_surface_normalize_fallback_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_fallback_recursive_grouping_spine_tree refined =
      phase1_surface_fallback_base_choice_spine_tree previous.
Proof.
  intros previous refined Hnormalize.
  unfold phase1_surface_fallback_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_fallback_recursive_grouping_spine_round_trip
      previous refined Hnormalize).
  reflexivity.
Qed.

Definition phase1_surface_normalize_fallback_recursive_grouping_tree
  (tree : ParseTree) : option Phase1SurfaceFallbackRecursiveGroupingSpine :=
  match phase1_surface_normalize_fallback_base_choice_spine tree with
  | Some previous =>
      phase1_surface_normalize_fallback_recursive_grouping_spine previous
  | None => None
  end.

Theorem phase1_surface_normalize_fallback_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_fallback_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_fallback_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_fallback_recursive_grouping_tree in Hnormalize.
  destruct (phase1_surface_normalize_fallback_base_choice_spine tree)
    as [previous |] eqn:Hprevious; try discriminate Hnormalize.
  transitivity (phase1_surface_fallback_base_choice_spine_tree previous).
  - eapply
      phase1_surface_normalize_fallback_recursive_grouping_spine_tree_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_fallback_base_choice_spine_round_trip.
    exact Hprevious.
Qed.

Definition phase1_surface_refine_fallback_recursive_grouping
  (previous : Phase1SurfaceFallbackBaseChoiceSpine)
  : option Phase1SurfaceFallbackRecursiveGroupingSpine :=
  phase1_surface_normalize_fallback_recursive_grouping_spine previous.

Theorem phase1_surface_refine_fallback_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_fallback_recursive_grouping previous = Some refined ->
    phase1_surface_fallback_recursive_grouping_spine_tree refined =
      phase1_surface_fallback_base_choice_spine_tree previous.
Proof.
  exact phase1_surface_normalize_fallback_recursive_grouping_spine_tree_round_trip.
Qed.
