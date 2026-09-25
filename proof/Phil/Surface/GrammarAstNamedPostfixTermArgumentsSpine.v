From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixStaticProjectionSpineTotality
  GrammarAstTermArgumentsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the term_arguments boundary in the term-leading
  named_postfix_expression tail:

    term_arguments, { ".", identifier }

  The static-leading branch is now fully refined through its repeated
  projections.  This focused slice leaves that branch unchanged and advances
  only the term-leading branch's term_arguments subtree to the reusable
  term-arguments carrier.  Its repeated projections remain an exact certified
  ParseTree for the next successor refinement.
*)

Inductive Phase1SurfaceNamedPostfixTermArgumentsSpine : Type :=
| Phase1NamedPostfixStaticRetainedAfterTermArguments
    (static_arguments : Phase1SurfaceStaticArgumentsSpine)
    (term_arguments : option Phase1SurfaceTermArgumentsSpine)
    (projections : list string)
| Phase1NamedPostfixTermArgumentsRefined
    (term_arguments : Phase1SurfaceTermArgumentsSpine)
    (projections : ParseTree).

Definition phase1_surface_named_postfix_term_arguments_spine_tree
  (tail : Phase1SurfaceNamedPostfixTermArgumentsSpine) : ParseTree :=
  match tail with
  | Phase1NamedPostfixStaticRetainedAfterTermArguments
      static_arguments term_arguments projections =>
      PTAlternative 0
        (PTSequence
          [ phase1_surface_static_arguments_spine_tree static_arguments;
            phase1_surface_named_postfix_optional_term_arguments_tree
              term_arguments;
            PTRepetition
              (map (phase1_surface_name_suffix_tree ".") projections)
          ])
  | Phase1NamedPostfixTermArgumentsRefined term_arguments projections =>
      PTAlternative 1
        (PTSequence
          [ phase1_surface_term_arguments_spine_tree term_arguments;
            projections
          ])
  end.

Definition phase1_surface_normalize_named_postfix_term_arguments_spine
  (tail : Phase1SurfaceNamedPostfixStaticProjectionSpine)
  : option Phase1SurfaceNamedPostfixTermArgumentsSpine :=
  match tail with
  | Phase1NamedPostfixStaticProjectionRefined
      static_arguments term_arguments projections =>
      Some
        (Phase1NamedPostfixStaticRetainedAfterTermArguments
          static_arguments term_arguments projections)
  | Phase1NamedPostfixTermRetainedAfterStaticProjection selected =>
      match phase1_surface_expect_sequence selected with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (term_arguments_tree, projections) =>
              match
                phase1_surface_normalize_term_arguments_spine
                  term_arguments_tree
              with
              | Some term_arguments =>
                  Some
                    (Phase1NamedPostfixTermArgumentsRefined
                      term_arguments projections)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_named_postfix_term_arguments_spine_round_trip :
  forall tail refined,
    phase1_surface_normalize_named_postfix_term_arguments_spine tail =
      Some refined ->
    phase1_surface_named_postfix_term_arguments_spine_tree refined =
      phase1_surface_named_postfix_static_projection_spine_tree tail.
Proof.
  intros tail refined Hnormalize.
  destruct tail as
    [static_arguments term_arguments projections | selected].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_expect_sequence selected)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[term_arguments_tree projections] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_arguments_spine term_arguments_tree)
      as [term_arguments |] eqn:Hterm_arguments;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_expect_sequence_round_trip
        selected items Hsequence).
    rewrite
      (phase1_surface_exact2_round_trip
        items term_arguments_tree projections Hitems).
    rewrite
      (phase1_surface_normalize_term_arguments_spine_round_trip
        term_arguments_tree term_arguments Hterm_arguments).
    reflexivity.
Qed.

Definition phase1_surface_normalize_named_postfix_term_arguments_tree
  (tree : ParseTree)
  : option Phase1SurfaceNamedPostfixTermArgumentsSpine :=
  match phase1_surface_normalize_named_postfix_static_projection_tree tree with
  | Some tail =>
      phase1_surface_normalize_named_postfix_term_arguments_spine tail
  | None => None
  end.

Theorem
  phase1_surface_normalize_named_postfix_term_arguments_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_named_postfix_term_arguments_tree tree =
      Some refined ->
    phase1_surface_named_postfix_term_arguments_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_named_postfix_term_arguments_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_named_postfix_static_projection_tree tree)
    as [tail |] eqn:Htail; try discriminate Hnormalize.
  transitivity
    (phase1_surface_named_postfix_static_projection_spine_tree tail).
  - eapply
      phase1_surface_normalize_named_postfix_term_arguments_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_named_postfix_static_projection_tree_round_trip.
    exact Htail.
Qed.
