From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixExpressionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Open the next retained boundary beneath named_postfix_expression:

    [ static_arguments, [ term_arguments ], { ".", identifier }
      | term_arguments, { ".", identifier } ]

  The outer optional shell and qualified-name prefix are already refined by
  GrammarAstNamedPostfixExpressionSpine.  This focused slice exposes only the
  static-leading-vs-term-leading choice of a present postfix tail.  The chosen
  branch body remains its exact certified ParseTree so static arguments, term
  arguments, and repeated projections can be refined independently in
  successor slices.
*)

Inductive Phase1SurfaceNamedPostfixTailChoiceSpine : Type :=
| Phase1SurfaceNamedPostfixTailStatic
    (selected : ParseTree)
| Phase1SurfaceNamedPostfixTailTerm
    (selected : ParseTree).

Definition phase1_surface_named_postfix_tail_choice_spine_tree
  (tail : Phase1SurfaceNamedPostfixTailChoiceSpine) : ParseTree :=
  match tail with
  | Phase1SurfaceNamedPostfixTailStatic selected =>
      PTAlternative 0 selected
  | Phase1SurfaceNamedPostfixTailTerm selected =>
      PTAlternative 1 selected
  end.

Definition phase1_surface_normalize_named_postfix_tail_choice_spine
  (tree : ParseTree) : option Phase1SurfaceNamedPostfixTailChoiceSpine :=
  match phase1_surface_expect_alternative tree with
  | Some (0, selected) =>
      Some (Phase1SurfaceNamedPostfixTailStatic selected)
  | Some (1, selected) =>
      Some (Phase1SurfaceNamedPostfixTailTerm selected)
  | _ => None
  end.

Theorem phase1_surface_normalize_named_postfix_tail_choice_spine_round_trip :
  forall tree tail,
    phase1_surface_normalize_named_postfix_tail_choice_spine tree = Some tail ->
    phase1_surface_named_postfix_tail_choice_spine_tree tail = tree.
Proof.
  intros tree tail Hnormalize.
  unfold phase1_surface_normalize_named_postfix_tail_choice_spine in Hnormalize.
  destruct (phase1_surface_expect_alternative tree)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - inversion Hnormalize; subst tail.
    unfold phase1_surface_named_postfix_tail_choice_spine_tree.
    rewrite
      (phase1_surface_expect_alternative_round_trip
        tree 0 selected Halternative).
    reflexivity.
  - destruct index as [|index].
    + inversion Hnormalize; subst tail.
      unfold phase1_surface_named_postfix_tail_choice_spine_tree.
      rewrite
        (phase1_surface_expect_alternative_round_trip
          tree 1 selected Halternative).
      reflexivity.
    + discriminate Hnormalize.
Qed.
