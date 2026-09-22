From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstExpressionOuterSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Open the next retained runtime-expression boundary:

    base_expression = command_expression | shift_expression ;

  This slice closes only that exact two-way choice.  The command-expression
  family and the shift-expression precedence graph remain exact certified
  ParseTree values for dedicated successor refinements.
*)

Inductive Phase1SurfaceBaseExpressionChoiceSpine : Type :=
| Phase1BaseExpressionCommand
    (command : ParseTree)
| Phase1BaseExpressionShift
    (shift : ParseTree).

Definition phase1_surface_base_expression_choice_spine_tree
  (expression : Phase1SurfaceBaseExpressionChoiceSpine) : ParseTree :=
  match expression with
  | Phase1BaseExpressionCommand command =>
      PTNonterminal "base_expression"
        (PTAlternative 0 command)
  | Phase1BaseExpressionShift shift =>
      PTNonterminal "base_expression"
        (PTAlternative 1 shift)
  end.

Definition phase1_surface_normalize_base_expression_choice_spine
  (tree : ParseTree) : option Phase1SurfaceBaseExpressionChoiceSpine :=
  match phase1_surface_expect_nonterminal "base_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match
            phase1_surface_validate_named_node "command_expression" selected
          with
          | Some tt => Some (Phase1BaseExpressionCommand selected)
          | None => None
          end
      | Some (1, selected) =>
          match
            phase1_surface_validate_named_node "shift_expression" selected
          with
          | Some tt => Some (Phase1BaseExpressionShift selected)
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_base_expression_choice_spine_round_trip :
  forall tree expression,
    phase1_surface_normalize_base_expression_choice_spine tree =
      Some expression ->
    phase1_surface_base_expression_choice_spine_tree expression = tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_base_expression_choice_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "base_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct
      (phase1_surface_validate_named_node "command_expression" selected)
      as [[] |] eqn:Hcommand; try discriminate Hnormalize.
    inversion Hnormalize; subst expression.
    unfold phase1_surface_base_expression_choice_spine_tree.
    rewrite
      (phase1_surface_expect_nonterminal_round_trip
        "base_expression" tree body Hnode).
    rewrite
      (phase1_surface_expect_alternative_round_trip
        body 0 selected Halternative).
    reflexivity.
  - destruct index as [|index].
    + destruct
        (phase1_surface_validate_named_node "shift_expression" selected)
        as [[] |] eqn:Hshift; try discriminate Hnormalize.
      inversion Hnormalize; subst expression.
      unfold phase1_surface_base_expression_choice_spine_tree.
      rewrite
        (phase1_surface_expect_nonterminal_round_trip
          "base_expression" tree body Hnode).
      rewrite
        (phase1_surface_expect_alternative_round_trip
          body 1 selected Halternative).
      reflexivity.
    + discriminate Hnormalize.
Qed.
