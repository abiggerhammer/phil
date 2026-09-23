From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermArgumentsExpressionOuterSpine
  GrammarAstExpressionFallbackBaseChoiceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the fully choice-refined ordinary-expression shell through
  term_arguments.

  Each argument advances from Phase1SurfaceExpressionOuterSpine to
  Phase1SurfaceExpressionFallbackBaseChoiceSpine, thereby certifying both the
  command/shift base_expression choice and the fail/reject fallback choice.
  Parenthesis/comma syntax and argument order remain exact.
*)

Definition
  phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine
  (expression : Phase1SurfaceExpressionOuterSpine)
  : option Phase1SurfaceExpressionFallbackBaseChoiceSpine :=
  match phase1_surface_normalize_expression_base_choice_spine expression with
  | Some base =>
      phase1_surface_normalize_expression_fallback_base_choice_spine base
  | None => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine
      expression = Some refined ->
    phase1_surface_expression_fallback_base_choice_spine_tree refined =
      phase1_surface_expression_outer_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine
    in Hnormalize.
  destruct (phase1_surface_normalize_expression_base_choice_spine expression)
    as [base |] eqn:Hbase; try discriminate Hnormalize.
  transitivity (phase1_surface_expression_base_choice_spine_tree base).
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_expression_base_choice_spine_round_trip.
    exact Hbase.
Qed.

Fixpoint
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
  (arguments : list Phase1SurfaceExpressionOuterSpine)
  : option (list Phase1SurfaceExpressionFallbackBaseChoiceSpine) :=
  match arguments with
  | [] => Some []
  | argument :: rest =>
      match
        phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine
          argument,
        phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
          rest
      with
      | Some refined, Some refined_rest =>
          Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_values_round_trip :
  forall arguments refined,
    phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
      arguments = Some refined ->
    map phase1_surface_expression_fallback_base_choice_spine_tree refined =
      map phase1_surface_expression_outer_spine_tree arguments.
Proof.
  intros arguments.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine
        argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
        rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine_round_trip.
      exact Hargument.
    + eapply IH.
      exact Hrest.
Qed.

Definition
  phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
  (argument : Phase1SurfaceExpressionFallbackBaseChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_expression_fallback_base_choice_spine_tree argument
    ].

Definition
  phase1_surface_term_argument_expression_fallback_base_choice_entries_tree
  (arguments : list Phase1SurfaceExpressionFallbackBaseChoiceSpine) : ParseTree :=
  match arguments with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_expression_fallback_base_choice_spine_tree first;
            PTRepetition
              (map
                phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree
                rest)
          ])
  end.

Theorem
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_values_entries_round_trip :
  forall arguments refined,
    phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
      arguments = Some refined ->
    phase1_surface_term_argument_expression_fallback_base_choice_entries_tree
      refined =
      phase1_surface_term_argument_expression_outer_entries_tree arguments.
Proof.
  intros arguments.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine
        argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
        rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine_round_trip
        argument actual Hargument).
    pose proof
      (phase1_surface_normalize_term_argument_expression_fallback_base_choice_values_round_trip
        rest actual_rest Hrest) as Hrest_round_trip.
    unfold
      phase1_surface_term_argument_expression_fallback_base_choice_suffix_tree.
    unfold phase1_surface_term_argument_expression_outer_suffix_tree.
    cbn in Hrest_round_trip |- *.
    rewrite Hrest_round_trip.
    reflexivity.
Qed.

Record Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine : Type := {
  phase1_term_arguments_expression_fallback_base_choice_spine_arguments :
    list Phase1SurfaceExpressionFallbackBaseChoiceSpine
}.

Definition phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
  (arguments : Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine)
  : ParseTree :=
  PTNonterminal "term_arguments"
    (PTSequence
      [ PTLiteral "(";
        phase1_surface_term_argument_expression_fallback_base_choice_entries_tree
          (phase1_term_arguments_expression_fallback_base_choice_spine_arguments
            arguments);
        PTLiteral ")"
      ]).

Definition
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine
  (arguments : Phase1SurfaceTermArgumentsExpressionOuterSpine)
  : option Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine :=
  match
    phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
      (phase1_term_arguments_expression_outer_spine_arguments arguments)
  with
  | Some refined =>
      Some
        {| phase1_term_arguments_expression_fallback_base_choice_spine_arguments :=
             refined |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine_round_trip :
  forall arguments refined,
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine
      arguments = Some refined ->
    phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
      refined =
      phase1_surface_term_arguments_expression_outer_spine_tree arguments.
Proof.
  intros [values] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
      values)
    as [actual |] eqn:Hvalues; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_term_argument_expression_fallback_base_choice_values_entries_round_trip
      values actual Hvalues).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree
  (tree : ParseTree)
  : option Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine :=
  match phase1_surface_normalize_term_arguments_expression_outer_tree tree with
  | Some arguments =>
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine
        arguments
  | None => None
  end.

Theorem
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree
      tree = Some refined ->
    phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_term_arguments_expression_outer_tree tree)
    as [arguments |] eqn:Harguments; try discriminate Hnormalize.
  transitivity
    (phase1_surface_term_arguments_expression_outer_spine_tree arguments).
  - eapply
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_term_arguments_expression_outer_tree_round_trip.
    exact Harguments.
Qed.
