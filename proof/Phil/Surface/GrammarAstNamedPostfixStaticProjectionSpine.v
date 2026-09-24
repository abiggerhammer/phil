From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixStaticTermArgumentsSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the repeated projection boundary inside the static-leading
  named_postfix_expression tail.

  The preceding slices have already advanced static_arguments and the optional
  term_arguments subtree.  This focused slice advances only the repeated
  ".", identifier projections to their semantic name-list carrier.  The
  term-leading branch remains an exact certified tree for its own successor
  refinement.
*)

Inductive Phase1SurfaceNamedPostfixStaticProjectionSpine : Type :=
| Phase1NamedPostfixStaticProjectionRefined
    (static_arguments : Phase1SurfaceStaticArgumentsSpine)
    (term_arguments : option Phase1SurfaceTermArgumentsSpine)
    (projections : list string)
| Phase1NamedPostfixTermRetainedAfterStaticProjection
    (selected : ParseTree).

Definition phase1_surface_named_postfix_static_projection_spine_tree
  (tail : Phase1SurfaceNamedPostfixStaticProjectionSpine) : ParseTree :=
  match tail with
  | Phase1NamedPostfixStaticProjectionRefined
      static_arguments term_arguments projections =>
      PTAlternative 0
        (PTSequence
          [ phase1_surface_static_arguments_spine_tree static_arguments;
            phase1_surface_named_postfix_optional_term_arguments_tree
              term_arguments;
            PTRepetition
              (map (phase1_surface_name_suffix_tree ".") projections)
          ])
  | Phase1NamedPostfixTermRetainedAfterStaticProjection selected =>
      PTAlternative 1 selected
  end.

Definition phase1_surface_normalize_named_postfix_static_projection_spine
  (tail : Phase1SurfaceNamedPostfixStaticTermArgumentsSpine)
  : option Phase1SurfaceNamedPostfixStaticProjectionSpine :=
  match tail with
  | Phase1NamedPostfixStaticTermArgumentsRefined
      static_arguments term_arguments projections_tree =>
      match phase1_surface_expect_repetition projections_tree with
      | Some projection_trees =>
          match
            phase1_surface_normalize_name_suffixes "." projection_trees
          with
          | Some projections =>
              Some
                (Phase1NamedPostfixStaticProjectionRefined
                  static_arguments term_arguments projections)
          | None => None
          end
      | None => None
      end
  | Phase1NamedPostfixTermRetainedAfterStaticTermArguments selected =>
      Some (Phase1NamedPostfixTermRetainedAfterStaticProjection selected)
  end.

Theorem
  phase1_surface_normalize_named_postfix_static_projection_spine_round_trip :
  forall tail refined,
    phase1_surface_normalize_named_postfix_static_projection_spine tail =
      Some refined ->
    phase1_surface_named_postfix_static_projection_spine_tree refined =
      phase1_surface_named_postfix_static_term_arguments_spine_tree tail.
Proof.
  intros tail refined Hnormalize.
  destruct tail as
    [static_arguments term_arguments projections_tree | selected].
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
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_named_postfix_static_projection_tree
  (tree : ParseTree)
  : option Phase1SurfaceNamedPostfixStaticProjectionSpine :=
  match
    phase1_surface_normalize_named_postfix_static_term_arguments_tree tree
  with
  | Some tail =>
      phase1_surface_normalize_named_postfix_static_projection_spine tail
  | None => None
  end.

Theorem
  phase1_surface_normalize_named_postfix_static_projection_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_named_postfix_static_projection_tree tree =
      Some refined ->
    phase1_surface_named_postfix_static_projection_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_named_postfix_static_projection_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_named_postfix_static_term_arguments_tree tree)
    as [tail |] eqn:Htail; try discriminate Hnormalize.
  transitivity
    (phase1_surface_named_postfix_static_term_arguments_spine_tree tail).
  - eapply
      phase1_surface_normalize_named_postfix_static_projection_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_named_postfix_static_term_arguments_tree_round_trip.
    exact Htail.
Qed.
