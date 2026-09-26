From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixTermArgumentsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the repeated projection boundary in the term-leading
  named_postfix_expression tail:

    term_arguments, { ".", identifier }

  The preceding slice has already advanced the term_arguments subtree.  This
  focused slice advances only the repeated projections to their semantic
  name-list carrier.  The fully refined static-leading branch remains
  unchanged.
*)

Inductive Phase1SurfaceNamedPostfixTermProjectionSpine : Type :=
| Phase1NamedPostfixStaticRetainedAfterTermProjection
    (static_arguments : Phase1SurfaceStaticArgumentsSpine)
    (term_arguments : option Phase1SurfaceTermArgumentsSpine)
    (projections : list string)
| Phase1NamedPostfixTermProjectionRefined
    (term_arguments : Phase1SurfaceTermArgumentsSpine)
    (projections : list string).

Definition phase1_surface_named_postfix_term_projection_spine_tree
  (tail : Phase1SurfaceNamedPostfixTermProjectionSpine) : ParseTree :=
  match tail with
  | Phase1NamedPostfixStaticRetainedAfterTermProjection
      static_arguments term_arguments projections =>
      PTAlternative 0
        (PTSequence
          [ phase1_surface_static_arguments_spine_tree static_arguments;
            phase1_surface_named_postfix_optional_term_arguments_tree
              term_arguments;
            PTRepetition
              (map (phase1_surface_name_suffix_tree ".") projections)
          ])
  | Phase1NamedPostfixTermProjectionRefined term_arguments projections =>
      PTAlternative 1
        (PTSequence
          [ phase1_surface_term_arguments_spine_tree term_arguments;
            PTRepetition
              (map (phase1_surface_name_suffix_tree ".") projections)
          ])
  end.

Definition phase1_surface_normalize_named_postfix_term_projection_spine
  (tail : Phase1SurfaceNamedPostfixTermArgumentsSpine)
  : option Phase1SurfaceNamedPostfixTermProjectionSpine :=
  match tail with
  | Phase1NamedPostfixStaticRetainedAfterTermArguments
      static_arguments term_arguments projections =>
      Some
        (Phase1NamedPostfixStaticRetainedAfterTermProjection
          static_arguments term_arguments projections)
  | Phase1NamedPostfixTermArgumentsRefined
      term_arguments projections_tree =>
      match phase1_surface_expect_repetition projections_tree with
      | Some projection_trees =>
          match
            phase1_surface_normalize_name_suffixes "." projection_trees
          with
          | Some projections =>
              Some
                (Phase1NamedPostfixTermProjectionRefined
                  term_arguments projections)
          | None => None
          end
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_named_postfix_term_projection_spine_round_trip :
  forall tail refined,
    phase1_surface_normalize_named_postfix_term_projection_spine tail =
      Some refined ->
    phase1_surface_named_postfix_term_projection_spine_tree refined =
      phase1_surface_named_postfix_term_arguments_spine_tree tail.
Proof.
  intros tail refined Hnormalize.
  destruct tail as
    [static_arguments term_arguments projections
    | term_arguments projections_tree].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_expect_repetition projections_tree)
      as [projection_trees |] eqn:Hrepetition;
      try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_name_suffixes "." projection_trees)
      as [projections |] eqn:Hprojections;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_expect_repetition_round_trip
        projections_tree projection_trees Hrepetition).
    rewrite <-
      (phase1_surface_normalize_name_suffixes_round_trip
        "." projection_trees projections Hprojections).
    reflexivity.
Qed.

Definition phase1_surface_normalize_named_postfix_term_projection_tree
  (tree : ParseTree)
  : option Phase1SurfaceNamedPostfixTermProjectionSpine :=
  match phase1_surface_normalize_named_postfix_term_arguments_tree tree with
  | Some tail =>
      phase1_surface_normalize_named_postfix_term_projection_spine tail
  | None => None
  end.

Theorem
  phase1_surface_normalize_named_postfix_term_projection_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_named_postfix_term_projection_tree tree =
      Some refined ->
    phase1_surface_named_postfix_term_projection_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_named_postfix_term_projection_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_named_postfix_term_arguments_tree tree)
    as [tail |] eqn:Htail; try discriminate Hnormalize.
  transitivity
    (phase1_surface_named_postfix_term_arguments_spine_tree tail).
  - eapply
      phase1_surface_normalize_named_postfix_term_projection_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_named_postfix_term_arguments_tree_round_trip.
    exact Htail.
Qed.
