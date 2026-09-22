From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstExpressionOuterSpine
  GrammarAstBaseExpressionChoiceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Advance the ordinary-expression shell by replacing its raw base_expression
  subtree with the certified two-way command/shift choice carrier.

  The optional fallback payload remains exact for a later refinement.
*)

Record Phase1SurfaceExpressionBaseChoiceSpine : Type := {
  phase1_expression_base_choice_spine_base :
    Phase1SurfaceBaseExpressionChoiceSpine;
  phase1_expression_base_choice_spine_fallback : option ParseTree
}.

Definition phase1_surface_expression_base_choice_spine_tree
  (expression : Phase1SurfaceExpressionBaseChoiceSpine) : ParseTree :=
  PTNonterminal "expression"
    (PTSequence
      [ phase1_surface_base_expression_choice_spine_tree
          (phase1_expression_base_choice_spine_base expression);
        phase1_surface_optional_expression_fallback_tree
          (phase1_expression_base_choice_spine_fallback expression)
      ]).

Definition phase1_surface_normalize_expression_base_choice_spine
  (expression : Phase1SurfaceExpressionOuterSpine)
  : option Phase1SurfaceExpressionBaseChoiceSpine :=
  match
    phase1_surface_normalize_base_expression_choice_spine
      (phase1_expression_outer_spine_base expression)
  with
  | Some base =>
      Some
        {| phase1_expression_base_choice_spine_base := base;
           phase1_expression_base_choice_spine_fallback :=
             phase1_expression_outer_spine_fallback expression |}
  | None => None
  end.

Theorem phase1_surface_normalize_expression_base_choice_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_expression_base_choice_spine expression =
      Some refined ->
    phase1_surface_expression_base_choice_spine_tree refined =
      phase1_surface_expression_outer_spine_tree expression.
Proof.
  intros [base fallback] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_base_expression_choice_spine base)
    as [actual |] eqn:Hbase; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_base_expression_choice_spine_round_trip
      base actual Hbase).
  reflexivity.
Qed.

Definition phase1_surface_normalize_expression_base_choice_tree
  (tree : ParseTree) : option Phase1SurfaceExpressionBaseChoiceSpine :=
  match phase1_surface_normalize_expression_outer_spine tree with
  | Some expression =>
      phase1_surface_normalize_expression_base_choice_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_expression_base_choice_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_expression_base_choice_tree tree =
      Some refined ->
    phase1_surface_expression_base_choice_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_expression_base_choice_tree in Hnormalize.
  destruct (phase1_surface_normalize_expression_outer_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity (phase1_surface_expression_outer_spine_tree expression).
  - eapply phase1_surface_normalize_expression_base_choice_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_expression_outer_spine_round_trip.
    exact Hexpression.
Qed.
