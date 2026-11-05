From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstExpressionFallbackBaseChoiceShiftSpine
  GrammarAstBaseExpressionShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the completed shift-expression refinement through the already
  fallback/base-choice-refined ordinary-expression shell.

  The optional fallback branch remains unchanged.  Only the base_expression
  field advances from Phase1SurfaceBaseExpressionShiftSpine to
  Phase1SurfaceBaseExpressionShiftRefinedSpine in this focused slice.
*)

Record Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine : Type := {
  phase1_expression_fallback_base_choice_shift_refined_spine_base :
    Phase1SurfaceBaseExpressionShiftRefinedSpine;
  phase1_expression_fallback_base_choice_shift_refined_spine_fallback :
    option Phase1SurfaceFallbackBaseChoiceSpine
}.

Definition phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
  (expression : Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTNonterminal "expression"
    (PTSequence
      [ phase1_surface_base_expression_shift_refined_spine_tree
          (phase1_expression_fallback_base_choice_shift_refined_spine_base
            expression);
        phase1_surface_optional_expression_fallback_base_choice_tree
          (phase1_expression_fallback_base_choice_shift_refined_spine_fallback
            expression)
      ]).

Definition
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel
  (fuel : nat)
  (expression : Phase1SurfaceExpressionFallbackBaseChoiceShiftSpine)
  : option Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_base_expression_shift_refined_spine_fuel
      fuel
      (phase1_expression_fallback_base_choice_shift_spine_base expression)
  with
  | Some base =>
      Some
        {| phase1_expression_fallback_base_choice_shift_refined_spine_base :=
             base;
           phase1_expression_fallback_base_choice_shift_refined_spine_fallback :=
             phase1_expression_fallback_base_choice_shift_spine_fallback
               expression |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip :
  forall fuel expression refined,
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
      phase1_surface_expression_fallback_base_choice_shift_spine_tree expression.
Proof.
  intros fuel [base fallback] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_base_expression_shift_refined_spine_fuel fuel base)
    as [actual |] eqn:Hbase; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_base_expression_shift_refined_spine_fuel_round_trip
      fuel base actual Hbase).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match phase1_surface_normalize_expression_fallback_base_choice_shift_tree tree
  with
  | Some expression =>
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_shift_tree tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity
    (phase1_surface_expression_fallback_base_choice_shift_spine_tree expression).
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_shift_tree_round_trip.
    exact Hexpression.
Qed.
