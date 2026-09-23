From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstExpressionFallbackBaseChoiceSpine
  GrammarAstBaseExpressionShiftSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the shift-refined base_expression carrier from #1355 through the
  already fallback/base-choice-refined ordinary-expression shell.

  The optional fallback branch remains unchanged.  Only the base_expression
  field advances from Phase1SurfaceBaseExpressionChoiceSpine to
  Phase1SurfaceBaseExpressionShiftSpine in this focused slice.
*)

Record Phase1SurfaceExpressionFallbackBaseChoiceShiftSpine : Type := {
  phase1_expression_fallback_base_choice_shift_spine_base :
    Phase1SurfaceBaseExpressionShiftSpine;
  phase1_expression_fallback_base_choice_shift_spine_fallback :
    option Phase1SurfaceFallbackBaseChoiceSpine
}.

Definition phase1_surface_expression_fallback_base_choice_shift_spine_tree
  (expression : Phase1SurfaceExpressionFallbackBaseChoiceShiftSpine)
  : ParseTree :=
  PTNonterminal "expression"
    (PTSequence
      [ phase1_surface_base_expression_shift_spine_tree
          (phase1_expression_fallback_base_choice_shift_spine_base expression);
        phase1_surface_optional_expression_fallback_base_choice_tree
          (phase1_expression_fallback_base_choice_shift_spine_fallback expression)
      ]).

Definition phase1_surface_normalize_expression_fallback_base_choice_shift_spine
  (expression : Phase1SurfaceExpressionFallbackBaseChoiceSpine)
  : option Phase1SurfaceExpressionFallbackBaseChoiceShiftSpine :=
  match
    phase1_surface_normalize_base_expression_shift_spine
      (phase1_expression_fallback_base_choice_spine_base expression)
  with
  | Some base =>
      Some
        {| phase1_expression_fallback_base_choice_shift_spine_base := base;
           phase1_expression_fallback_base_choice_shift_spine_fallback :=
             phase1_expression_fallback_base_choice_spine_fallback expression |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_shift_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_expression_fallback_base_choice_shift_spine
      expression = Some refined ->
    phase1_surface_expression_fallback_base_choice_shift_spine_tree refined =
      phase1_surface_expression_fallback_base_choice_spine_tree expression.
Proof.
  intros [base fallback] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_base_expression_shift_spine base)
    as [actual |] eqn:Hbase; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_base_expression_shift_spine_round_trip
      base actual Hbase).
  reflexivity.
Qed.

Definition phase1_surface_normalize_expression_fallback_base_choice_shift_tree
  (tree : ParseTree)
  : option Phase1SurfaceExpressionFallbackBaseChoiceShiftSpine :=
  match phase1_surface_normalize_expression_fallback_base_choice_tree tree with
  | Some expression =>
      phase1_surface_normalize_expression_fallback_base_choice_shift_spine
        expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_shift_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_expression_fallback_base_choice_shift_tree tree =
      Some refined ->
    phase1_surface_expression_fallback_base_choice_shift_spine_tree refined =
      tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_expression_fallback_base_choice_shift_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_expression_fallback_base_choice_tree tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity
    (phase1_surface_expression_fallback_base_choice_spine_tree expression).
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_shift_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_tree_round_trip.
    exact Hexpression.
Qed.
