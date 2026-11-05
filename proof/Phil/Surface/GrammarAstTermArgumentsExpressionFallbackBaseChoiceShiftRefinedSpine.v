From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceSpine
  GrammarAstExpressionFallbackBaseChoiceShiftSpine
  GrammarAstExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

Definition
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
  (fuel : nat)
  (expression : Phase1SurfaceExpressionFallbackBaseChoiceSpine)
  : option Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_expression_fallback_base_choice_shift_spine
      expression
  with
  | Some shifted =>
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel shifted
  | None => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_round_trip :
  forall fuel expression refined,
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
      fuel expression = Some refined ->
    phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
      phase1_surface_expression_fallback_base_choice_spine_tree expression.
Proof.
  intros fuel expression refined Hnormalize.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_shift_spine
      expression)
    as [shifted |] eqn:Hshifted; try discriminate Hnormalize.
  transitivity
    (phase1_surface_expression_fallback_base_choice_shift_spine_tree shifted).
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_shift_spine_round_trip.
    exact Hshifted.
Qed.

Fixpoint
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
  (fuel : nat)
  (arguments : list Phase1SurfaceExpressionFallbackBaseChoiceSpine)
  : option (list Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine) :=
  match arguments with
  | [] => Some []
  | argument :: rest =>
      match
        phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
          fuel argument,
        phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
          fuel rest
      with
      | Some refined, Some refined_rest =>
          Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_round_trip :
  forall fuel arguments refined,
    phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
      fuel arguments = Some refined ->
    map
      phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    map phase1_surface_expression_fallback_base_choice_spine_tree arguments.
Proof.
  intros fuel arguments.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
        fuel argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
        fuel rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_round_trip.
      exact Hargument.
    + eapply IH.
      exact Hrest.
Qed.

Definition
  phase1_surface_term_argument_expression_fallback_base_choice_shift_refined_suffix_tree
  (argument : Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
        argument
    ].

Definition
  phase1_surface_term_argument_expression_fallback_base_choice_shift_refined_entries_tree
  (arguments : list Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  match arguments with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
              first;
            PTRepetition
              (map
                phase1_surface_term_argument_expression_fallback_base_choice_shift_refined_suffix_tree
                rest)
          ])
  end.

Theorem
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_entries_fuel_round_trip :
  forall fuel arguments refined,
    phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
      fuel arguments = Some refined ->
    phase1_surface_term_argument_expression_fallback_base_choice_shift_refined_entries_tree
      refined =
    phase1_surface_term_argument_expression_fallback_base_choice_entries_tree
      arguments.
Proof.
  intros fuel arguments.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
        fuel argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
        fuel rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_round_trip
        fuel argument actual Hargument).
    pose proof
      (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel_round_trip
        fuel rest actual_rest Hrest) as Hrest_round_trip.
    unfold
      phase1_surface_term_argument_expression_fallback_base_choice_shift_refined_suffix_tree.
    unfold
      phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree.
    cbn in Hrest_round_trip |- *.
    rewrite Hrest_round_trip.
    reflexivity.
Qed.

Record
  Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  : Type := {
  phase1_term_arguments_expression_fallback_base_choice_shift_refined_spine_arguments :
    list Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine
}.

Definition
  phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
  (arguments :
    Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTNonterminal "term_arguments"
    (PTSequence
      [ PTLiteral "(";
        phase1_surface_term_argument_expression_fallback_base_choice_shift_refined_entries_tree
          (phase1_term_arguments_expression_fallback_base_choice_shift_refined_spine_arguments
            arguments);
        PTLiteral ")"
      ]).

Definition
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
  (fuel : nat)
  (arguments : Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine)
  : option
      Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
      fuel
      (phase1_term_arguments_expression_fallback_base_choice_spine_arguments
        arguments)
  with
  | Some refined =>
      Some
        {| phase1_term_arguments_expression_fallback_base_choice_shift_refined_spine_arguments :=
             refined |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip :
  forall fuel arguments refined,
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel arguments = Some refined ->
    phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
      arguments.
Proof.
  intros fuel [values] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_fuel
      fuel values)
    as [actual |] eqn:Hvalues; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_term_argument_expression_fallback_base_choice_shift_refined_values_entries_fuel_round_trip
      fuel values actual Hvalues).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option
      Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree
      tree
  with
  | Some arguments =>
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel arguments
  | None => None
  end.

Theorem
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree
      tree)
    as [arguments |] eqn:Harguments; try discriminate Hnormalize.
  transitivity
    (phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
      arguments).
  - eapply
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree_round_trip.
    exact Harguments.
Qed.
