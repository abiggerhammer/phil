From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstMultiplicativeExpressionSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Open the unary-expression precedence boundary retained beneath the
  multiplicative-expression refinement chain:

    unary_expression =
        "-", unary_expression
      | postfix_expression
      ;

  This slice exposes only the outer unary choice.  A negation operand remains
  an exact certified unary_expression ParseTree, and the postfix branch remains
  an exact certified postfix_expression ParseTree, for dedicated successor
  refinements.
*)

Inductive Phase1SurfaceUnaryExpressionSpine : Type :=
| Phase1SurfaceUnaryExpressionNegate
    (operand : ParseTree)
| Phase1SurfaceUnaryExpressionPostfix
    (postfix : ParseTree).

Definition phase1_surface_postfix_expression_node_tree
  (tree : ParseTree) : ParseTree := tree.

Definition phase1_surface_normalize_postfix_expression_node
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_validate_named_node "postfix_expression" tree with
  | Some tt => Some tree
  | None => None
  end.

Theorem phase1_surface_normalize_postfix_expression_node_round_trip :
  forall tree refined,
    phase1_surface_normalize_postfix_expression_node tree = Some refined ->
    phase1_surface_postfix_expression_node_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_postfix_expression_node in Hnormalize.
  destruct
    (phase1_surface_validate_named_node "postfix_expression" tree)
    as [[] |] eqn:Hvalidate; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  reflexivity.
Qed.

Definition phase1_surface_unary_expression_spine_tree
  (expression : Phase1SurfaceUnaryExpressionSpine) : ParseTree :=
  match expression with
  | Phase1SurfaceUnaryExpressionNegate operand =>
      PTNonterminal "unary_expression"
        (PTAlternative 0
          (PTSequence
            [ PTLiteral "-";
              phase1_surface_unary_expression_node_tree operand
            ]))
  | Phase1SurfaceUnaryExpressionPostfix postfix =>
      PTNonterminal "unary_expression"
        (PTAlternative 1
          (phase1_surface_postfix_expression_node_tree postfix))
  end.

Definition phase1_surface_normalize_unary_expression_spine
  (tree : ParseTree) : option Phase1SurfaceUnaryExpressionSpine :=
  match phase1_surface_expect_nonterminal "unary_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_expect_sequence selected with
          | Some items =>
              match phase1_surface_exact2 items with
              | Some (minus_tree, operand_tree) =>
                  match phase1_surface_expect_literal "-" minus_tree,
                        phase1_surface_normalize_unary_expression_node operand_tree with
                  | Some tt, Some operand =>
                      Some (Phase1SurfaceUnaryExpressionNegate operand)
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | Some (1, selected) =>
          match phase1_surface_normalize_postfix_expression_node selected with
          | Some postfix =>
              Some (Phase1SurfaceUnaryExpressionPostfix postfix)
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_unary_expression_spine_round_trip :
  forall tree expression,
    phase1_surface_normalize_unary_expression_spine tree = Some expression ->
    phase1_surface_unary_expression_spine_tree expression = tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_unary_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "unary_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_expect_sequence selected)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[minus_tree operand_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "-" minus_tree)
      as [[] |] eqn:Hminus; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_unary_expression_node operand_tree)
      as [operand |] eqn:Hoperand; try discriminate Hnormalize.
    inversion Hnormalize; subst expression.
    unfold phase1_surface_unary_expression_spine_tree.
    cbn.
    rewrite
      (phase1_surface_expect_nonterminal_round_trip
        "unary_expression" tree body Hnode).
    rewrite
      (phase1_surface_expect_alternative_round_trip
        body 0 selected Halternative).
    rewrite
      (phase1_surface_expect_sequence_round_trip selected items Hsequence).
    rewrite
      (phase1_surface_exact2_round_trip
        items minus_tree operand_tree Hitems).
    rewrite
      (phase1_surface_expect_literal_round_trip
        "-" minus_tree Hminus).
    rewrite
      (phase1_surface_normalize_unary_expression_node_round_trip
        operand_tree operand Hoperand).
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_normalize_postfix_expression_node selected)
        as [postfix |] eqn:Hpostfix; try discriminate Hnormalize.
      inversion Hnormalize; subst expression.
      unfold phase1_surface_unary_expression_spine_tree.
      cbn.
      rewrite
        (phase1_surface_expect_nonterminal_round_trip
          "unary_expression" tree body Hnode).
      rewrite
        (phase1_surface_expect_alternative_round_trip
          body 1 selected Halternative).
      rewrite
        (phase1_surface_normalize_postfix_expression_node_round_trip
          selected postfix Hpostfix).
      reflexivity.
    + discriminate Hnormalize.
Qed.
