From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixStaticArgumentsSpineTotality
  GrammarAstTermArgumentsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the optional term_arguments boundary inside the static-leading
  named_postfix_expression tail.

  The preceding slice has already advanced the leading static_arguments
  subtree.  This focused slice advances only the optional term_arguments shell
  of that same branch to the reusable term-arguments carrier.  Repeated
  projections remain exact certified trees, and the term-leading branch remains
  exact for its own successor refinement.
*)

Definition phase1_surface_named_postfix_optional_term_arguments_tree
  (arguments : option Phase1SurfaceTermArgumentsSpine) : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some arguments_value =>
      PTOptionalSome
        (phase1_surface_term_arguments_spine_tree arguments_value)
  end.

Definition phase1_surface_normalize_named_postfix_optional_term_arguments
  (tree : ParseTree)
  : option (option Phase1SurfaceTermArgumentsSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some arguments_tree) =>
      match phase1_surface_normalize_term_arguments_spine arguments_tree with
      | Some arguments => Some (Some arguments)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_named_postfix_optional_term_arguments_round_trip :
  forall tree arguments,
    phase1_surface_normalize_named_postfix_optional_term_arguments tree =
      Some arguments ->
    phase1_surface_named_postfix_optional_term_arguments_tree arguments = tree.
Proof.
  intros tree arguments Hnormalize.
  unfold phase1_surface_normalize_named_postfix_optional_term_arguments
    in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[arguments_tree |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_normalize_term_arguments_spine arguments_tree)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst arguments.
    unfold phase1_surface_named_postfix_optional_term_arguments_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some arguments_tree) Hoptional).
    rewrite
      (phase1_surface_normalize_term_arguments_spine_round_trip
        arguments_tree actual Harguments).
    reflexivity.
  - inversion Hnormalize; subst arguments.
    unfold phase1_surface_named_postfix_optional_term_arguments_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Inductive Phase1SurfaceNamedPostfixStaticTermArgumentsSpine : Type :=
| Phase1NamedPostfixStaticTermArgumentsRefined
    (static_arguments : Phase1SurfaceStaticArgumentsSpine)
    (term_arguments : option Phase1SurfaceTermArgumentsSpine)
    (projections : ParseTree)
| Phase1NamedPostfixTermRetainedAfterStaticTermArguments
    (selected : ParseTree).

Definition phase1_surface_named_postfix_static_term_arguments_spine_tree
  (tail : Phase1SurfaceNamedPostfixStaticTermArgumentsSpine) : ParseTree :=
  match tail with
  | Phase1NamedPostfixStaticTermArgumentsRefined
      static_arguments term_arguments projections =>
      PTAlternative 0
        (PTSequence
          [ phase1_surface_static_arguments_spine_tree static_arguments;
            phase1_surface_named_postfix_optional_term_arguments_tree
              term_arguments;
            projections
          ])
  | Phase1NamedPostfixTermRetainedAfterStaticTermArguments selected =>
      PTAlternative 1 selected
  end.

Definition phase1_surface_normalize_named_postfix_static_term_arguments_spine
  (tail : Phase1SurfaceNamedPostfixStaticArgumentsSpine)
  : option Phase1SurfaceNamedPostfixStaticTermArgumentsSpine :=
  match tail with
  | Phase1NamedPostfixStaticRefined
      static_arguments term_arguments_tree projections =>
      match
        phase1_surface_normalize_named_postfix_optional_term_arguments
          term_arguments_tree
      with
      | Some term_arguments =>
          Some
            (Phase1NamedPostfixStaticTermArgumentsRefined
              static_arguments term_arguments projections)
      | None => None
      end
  | Phase1NamedPostfixTermRetained selected =>
      Some (Phase1NamedPostfixTermRetainedAfterStaticTermArguments selected)
  end.

Theorem
  phase1_surface_normalize_named_postfix_static_term_arguments_spine_round_trip :
  forall tail refined,
    phase1_surface_normalize_named_postfix_static_term_arguments_spine tail =
      Some refined ->
    phase1_surface_named_postfix_static_term_arguments_spine_tree refined =
      phase1_surface_named_postfix_static_arguments_spine_tree tail.
Proof.
  intros tail refined Hnormalize.
  destruct tail as [static_arguments term_arguments_tree projections | selected].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_named_postfix_optional_term_arguments
        term_arguments_tree)
      as [term_arguments |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_named_postfix_optional_term_arguments_round_trip
        term_arguments_tree term_arguments Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_named_postfix_static_term_arguments_tree
  (tree : ParseTree)
  : option Phase1SurfaceNamedPostfixStaticTermArgumentsSpine :=
  match phase1_surface_normalize_named_postfix_static_arguments_tree tree with
  | Some tail =>
      phase1_surface_normalize_named_postfix_static_term_arguments_spine tail
  | None => None
  end.

Theorem
  phase1_surface_normalize_named_postfix_static_term_arguments_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_named_postfix_static_term_arguments_tree tree =
      Some refined ->
    phase1_surface_named_postfix_static_term_arguments_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_named_postfix_static_term_arguments_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_named_postfix_static_arguments_tree tree)
    as [tail |] eqn:Htail; try discriminate Hnormalize.
  transitivity
    (phase1_surface_named_postfix_static_arguments_spine_tree tail).
  - eapply
      phase1_surface_normalize_named_postfix_static_term_arguments_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_named_postfix_static_arguments_tree_round_trip.
    exact Htail.
Qed.
