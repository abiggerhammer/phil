From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermArgumentsSpine
  GrammarAstExpressionOuterSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the outer ordinary-expression carrier through term_arguments.

  The term-argument list shell was already closed by #1243/#1245. This layer
  advances each certified expression ParseTree to Phase1SurfaceExpressionOuterSpine
  while preserving exact parenthesis/comma syntax and source order.
*)

Fixpoint phase1_surface_normalize_term_argument_expression_outer_values
  (arguments : list ParseTree)
  : option (list Phase1SurfaceExpressionOuterSpine) :=
  match arguments with
  | [] => Some []
  | argument :: rest =>
      match phase1_surface_normalize_expression_outer_spine argument,
            phase1_surface_normalize_term_argument_expression_outer_values rest
      with
      | Some refined, Some refined_rest =>
          Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_term_argument_expression_outer_values_round_trip :
  forall arguments refined,
    phase1_surface_normalize_term_argument_expression_outer_values arguments =
      Some refined ->
    map phase1_surface_expression_outer_spine_tree refined = arguments.
Proof.
  intros arguments.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_expression_outer_spine argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_argument_expression_outer_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_expression_outer_spine_round_trip.
      exact Hargument.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_term_argument_expression_outer_suffix_tree
  (argument : Phase1SurfaceExpressionOuterSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_expression_outer_spine_tree argument
    ].

Definition phase1_surface_term_argument_expression_outer_entries_tree
  (arguments : list Phase1SurfaceExpressionOuterSpine) : ParseTree :=
  match arguments with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_expression_outer_spine_tree first;
            PTRepetition
              (map
                phase1_surface_term_argument_expression_outer_suffix_tree
                rest)
          ])
  end.

Theorem
  phase1_surface_normalize_term_argument_expression_outer_values_entries_round_trip :
  forall arguments refined,
    phase1_surface_normalize_term_argument_expression_outer_values arguments =
      Some refined ->
    phase1_surface_term_argument_expression_outer_entries_tree refined =
      phase1_surface_term_argument_entries_tree arguments.
Proof.
  intros arguments.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_expression_outer_spine argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_argument_expression_outer_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_expression_outer_spine_round_trip
        argument actual Hargument).
    pose proof
      (phase1_surface_normalize_term_argument_expression_outer_values_round_trip
        rest actual_rest Hrest) as Hrest_round_trip.
    unfold phase1_surface_term_argument_expression_outer_suffix_tree.
    unfold phase1_surface_term_argument_suffix_tree.
    cbn in Hrest_round_trip |- *.
    rewrite Hrest_round_trip.
    reflexivity.
Qed.

Record Phase1SurfaceTermArgumentsExpressionOuterSpine : Type := {
  phase1_term_arguments_expression_outer_spine_arguments :
    list Phase1SurfaceExpressionOuterSpine
}.

Definition phase1_surface_term_arguments_expression_outer_spine_tree
  (arguments : Phase1SurfaceTermArgumentsExpressionOuterSpine) : ParseTree :=
  PTNonterminal "term_arguments"
    (PTSequence
      [ PTLiteral "(";
        phase1_surface_term_argument_expression_outer_entries_tree
          (phase1_term_arguments_expression_outer_spine_arguments arguments);
        PTLiteral ")"
      ]).

Definition phase1_surface_normalize_term_arguments_expression_outer_spine
  (arguments : Phase1SurfaceTermArgumentsSpine)
  : option Phase1SurfaceTermArgumentsExpressionOuterSpine :=
  match
    phase1_surface_normalize_term_argument_expression_outer_values
      (phase1_term_arguments_spine_arguments arguments)
  with
  | Some refined =>
      Some
        {| phase1_term_arguments_expression_outer_spine_arguments := refined |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_term_arguments_expression_outer_spine_round_trip :
  forall arguments refined,
    phase1_surface_normalize_term_arguments_expression_outer_spine arguments =
      Some refined ->
    phase1_surface_term_arguments_expression_outer_spine_tree refined =
      phase1_surface_term_arguments_spine_tree arguments.
Proof.
  intros [values] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_term_argument_expression_outer_values values)
    as [actual |] eqn:Hvalues; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_term_argument_expression_outer_values_entries_round_trip
      values actual Hvalues).
  reflexivity.
Qed.

Definition phase1_surface_normalize_term_arguments_expression_outer_tree
  (tree : ParseTree)
  : option Phase1SurfaceTermArgumentsExpressionOuterSpine :=
  match phase1_surface_normalize_term_arguments_spine tree with
  | Some arguments =>
      phase1_surface_normalize_term_arguments_expression_outer_spine arguments
  | None => None
  end.

Theorem
  phase1_surface_normalize_term_arguments_expression_outer_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_term_arguments_expression_outer_tree tree =
      Some refined ->
    phase1_surface_term_arguments_expression_outer_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_term_arguments_expression_outer_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_term_arguments_spine tree)
    as [arguments |] eqn:Harguments; try discriminate Hnormalize.
  transitivity (phase1_surface_term_arguments_spine_tree arguments).
  - eapply
      phase1_surface_normalize_term_arguments_expression_outer_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_term_arguments_spine_round_trip.
    exact Harguments.
Qed.
