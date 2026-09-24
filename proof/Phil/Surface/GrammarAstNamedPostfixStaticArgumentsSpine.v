From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixTailChoiceSpineTotality
  GrammarAstStaticArgumentsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the static_arguments boundary inside the static-leading
  named_postfix_expression tail.

  The preceding tail-choice spine exposes the two alternatives exactly:

    static_arguments, [ term_arguments ], { ".", identifier }
  | term_arguments, { ".", identifier }

  This focused slice advances only the leading static_arguments subtree of the
  first branch to the existing reusable static-arguments carrier.  The optional
  term-arguments shell and repeated projections remain exact certified trees,
  and the term-leading branch remains exact for independent successor slices.
*)

Inductive Phase1SurfaceNamedPostfixStaticArgumentsSpine : Type :=
| Phase1NamedPostfixStaticRefined
    (arguments : Phase1SurfaceStaticArgumentsSpine)
    (term_arguments : ParseTree)
    (projections : ParseTree)
| Phase1NamedPostfixTermRetained
    (selected : ParseTree).

Definition phase1_surface_named_postfix_static_arguments_spine_tree
  (tail : Phase1SurfaceNamedPostfixStaticArgumentsSpine) : ParseTree :=
  match tail with
  | Phase1NamedPostfixStaticRefined arguments term_arguments projections =>
      PTAlternative 0
        (PTSequence
          [ phase1_surface_static_arguments_spine_tree arguments;
            term_arguments;
            projections
          ])
  | Phase1NamedPostfixTermRetained selected =>
      PTAlternative 1 selected
  end.

Definition phase1_surface_normalize_named_postfix_static_arguments_spine
  (tail : Phase1SurfaceNamedPostfixTailChoiceSpine)
  : option Phase1SurfaceNamedPostfixStaticArgumentsSpine :=
  match tail with
  | Phase1SurfaceNamedPostfixTailStatic selected =>
      match phase1_surface_expect_sequence selected with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (arguments_tree, term_arguments_tree, projections_tree) =>
              match
                phase1_surface_normalize_static_arguments_spine arguments_tree
              with
              | Some arguments =>
                  Some
                    (Phase1NamedPostfixStaticRefined
                      arguments term_arguments_tree projections_tree)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | Phase1SurfaceNamedPostfixTailTerm selected =>
      Some (Phase1NamedPostfixTermRetained selected)
  end.

Theorem phase1_surface_normalize_named_postfix_static_arguments_spine_round_trip :
  forall tail refined,
    phase1_surface_normalize_named_postfix_static_arguments_spine tail =
      Some refined ->
    phase1_surface_named_postfix_static_arguments_spine_tree refined =
      phase1_surface_named_postfix_tail_choice_spine_tree tail.
Proof.
  intros tail refined Hnormalize.
  destruct tail as [selected | selected].
  - cbn in Hnormalize.
    destruct (phase1_surface_expect_sequence selected)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact3 items)
      as [[[arguments_tree term_arguments_tree] projections_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_static_arguments_spine arguments_tree)
      as [arguments |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_expect_sequence_round_trip
      selected items Hsequence).
    rewrite (phase1_surface_exact3_round_trip
      items arguments_tree term_arguments_tree projections_tree Hitems).
    rewrite (phase1_surface_normalize_static_arguments_spine_round_trip
      arguments_tree arguments Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_named_postfix_static_arguments_tree
  (tree : ParseTree)
  : option Phase1SurfaceNamedPostfixStaticArgumentsSpine :=
  match phase1_surface_normalize_named_postfix_tail_choice_spine tree with
  | Some tail =>
      phase1_surface_normalize_named_postfix_static_arguments_spine tail
  | None => None
  end.

Theorem phase1_surface_normalize_named_postfix_static_arguments_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_named_postfix_static_arguments_tree tree =
      Some refined ->
    phase1_surface_named_postfix_static_arguments_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_named_postfix_static_arguments_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_named_postfix_tail_choice_spine tree)
    as [tail |] eqn:Htail; try discriminate Hnormalize.
  transitivity (phase1_surface_named_postfix_tail_choice_spine_tree tail).
  - eapply
      phase1_surface_normalize_named_postfix_static_arguments_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_named_postfix_tail_choice_spine_round_trip.
    exact Htail.
Qed.
