From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstExpressionBaseChoiceSpine
  GrammarAstFallbackBaseChoiceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Advance the ordinary-expression shell by replacing its raw optional fallback
  payload with the certified two-way fail/reject fallback choice carrier.

  The base_expression field remains at the certified command/shift choice
  boundary from the preceding expression refinement.
*)

Definition phase1_surface_expression_fallback_base_choice_tail_tree
  (fallback : Phase1SurfaceFallbackBaseChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral "or";
      phase1_surface_fallback_base_choice_spine_tree fallback
    ].

Definition phase1_surface_optional_expression_fallback_base_choice_tree
  (fallback : option Phase1SurfaceFallbackBaseChoiceSpine) : ParseTree :=
  match fallback with
  | None => PTOptionalNone
  | Some fallback_value =>
      PTOptionalSome
        (phase1_surface_expression_fallback_base_choice_tail_tree
          fallback_value)
  end.

Definition phase1_surface_normalize_optional_expression_fallback_base_choice
  (fallback : option ParseTree)
  : option (option Phase1SurfaceFallbackBaseChoiceSpine) :=
  match fallback with
  | None => Some None
  | Some tree =>
      match phase1_surface_normalize_fallback_base_choice_spine tree with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_optional_expression_fallback_base_choice_round_trip :
  forall fallback refined,
    phase1_surface_normalize_optional_expression_fallback_base_choice fallback =
      Some refined ->
    phase1_surface_optional_expression_fallback_base_choice_tree refined =
      phase1_surface_optional_expression_fallback_tree fallback.
Proof.
  intros [tree |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_fallback_base_choice_spine tree)
      as [actual |] eqn:Hfallback; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_fallback_base_choice_spine_round_trip
        tree actual Hfallback).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record Phase1SurfaceExpressionFallbackBaseChoiceSpine : Type := {
  phase1_expression_fallback_base_choice_spine_base :
    Phase1SurfaceBaseExpressionChoiceSpine;
  phase1_expression_fallback_base_choice_spine_fallback :
    option Phase1SurfaceFallbackBaseChoiceSpine
}.

Definition phase1_surface_expression_fallback_base_choice_spine_tree
  (expression : Phase1SurfaceExpressionFallbackBaseChoiceSpine) : ParseTree :=
  PTNonterminal "expression"
    (PTSequence
      [ phase1_surface_base_expression_choice_spine_tree
          (phase1_expression_fallback_base_choice_spine_base expression);
        phase1_surface_optional_expression_fallback_base_choice_tree
          (phase1_expression_fallback_base_choice_spine_fallback expression)
      ]).

Definition phase1_surface_normalize_expression_fallback_base_choice_spine
  (expression : Phase1SurfaceExpressionBaseChoiceSpine)
  : option Phase1SurfaceExpressionFallbackBaseChoiceSpine :=
  match
    phase1_surface_normalize_optional_expression_fallback_base_choice
      (phase1_expression_base_choice_spine_fallback expression)
  with
  | Some fallback =>
      Some
        {| phase1_expression_fallback_base_choice_spine_base :=
             phase1_expression_base_choice_spine_base expression;
           phase1_expression_fallback_base_choice_spine_fallback := fallback |}
  | None => None
  end.

Theorem phase1_surface_normalize_expression_fallback_base_choice_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_expression_fallback_base_choice_spine expression =
      Some refined ->
    phase1_surface_expression_fallback_base_choice_spine_tree refined =
      phase1_surface_expression_base_choice_spine_tree expression.
Proof.
  intros [base fallback] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_expression_fallback_base_choice fallback)
    as [actual |] eqn:Hfallback; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_expression_fallback_base_choice_round_trip
      fallback actual Hfallback).
  reflexivity.
Qed.

Definition phase1_surface_normalize_expression_fallback_base_choice_tree
  (tree : ParseTree)
  : option Phase1SurfaceExpressionFallbackBaseChoiceSpine :=
  match phase1_surface_normalize_expression_base_choice_tree tree with
  | Some expression =>
      phase1_surface_normalize_expression_fallback_base_choice_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_expression_fallback_base_choice_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_expression_fallback_base_choice_tree tree =
      Some refined ->
    phase1_surface_expression_fallback_base_choice_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_expression_fallback_base_choice_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_expression_base_choice_tree tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity (phase1_surface_expression_base_choice_spine_tree expression).
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_expression_base_choice_tree_round_trip.
    exact Hexpression.
Qed.
