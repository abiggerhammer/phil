From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Open the parenthesized-expression payload retained by the primary-expression
  outer spine:

    parenthesized_expression = "(", expression, ")" ;

  This focused slice validates the exact grouping shell while retaining the
  nested ordinary-expression tree for later expression-layer refinement.
*)

Record Phase1SurfaceParenthesizedExpressionSpine : Type := {
  phase1_parenthesized_expression_spine_expression : ParseTree
}.

Definition phase1_surface_parenthesized_expression_spine_tree
  (grouped : Phase1SurfaceParenthesizedExpressionSpine) : ParseTree :=
  PTNonterminal "parenthesized_expression"
    (PTSequence
      [ PTLiteral "(";
        phase1_parenthesized_expression_spine_expression grouped;
        PTLiteral ")"
      ]).

Definition phase1_surface_normalize_parenthesized_expression_spine
  (tree : ParseTree)
  : option Phase1SurfaceParenthesizedExpressionSpine :=
  match phase1_surface_expect_nonterminal "parenthesized_expression" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (open_tree, expression_tree, close_tree) =>
              match phase1_surface_expect_literal "(" open_tree,
                    phase1_surface_validate_named_node
                      "expression" expression_tree,
                    phase1_surface_expect_literal ")" close_tree with
              | Some tt, Some tt, Some tt =>
                  Some
                    {| phase1_parenthesized_expression_spine_expression :=
                         expression_tree |}
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_parenthesized_expression_spine_round_trip :
  forall tree grouped,
    phase1_surface_normalize_parenthesized_expression_spine tree =
      Some grouped ->
    phase1_surface_parenthesized_expression_spine_tree grouped = tree.
Proof.
  intros tree grouped Hnormalize.
  unfold phase1_surface_normalize_parenthesized_expression_spine in Hnormalize.
  destruct
    (phase1_surface_expect_nonterminal "parenthesized_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[open_tree expression_tree] close_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node "expression" expression_tree)
    as [[] |] eqn:Hexpression; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst grouped.
  unfold phase1_surface_parenthesized_expression_spine_tree.
  cbn.
  rewrite
    (phase1_surface_expect_nonterminal_round_trip
      "parenthesized_expression" tree body Hnode).
  rewrite
    (phase1_surface_expect_sequence_round_trip
      body items Hsequence).
  rewrite
    (phase1_surface_exact3_round_trip
      items open_tree expression_tree close_tree Hitems).
  rewrite
    (phase1_surface_expect_literal_round_trip
      "(" open_tree Hopen).
  rewrite
    (phase1_surface_expect_literal_round_trip
      ")" close_tree Hclose).
  reflexivity.
Qed.
