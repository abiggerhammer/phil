From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSourceHeader
  GrammarAstUnaryExpressionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Open the postfix-expression boundary retained beneath the unary-expression
  refinement chain:

    postfix_expression =
        named_postfix_expression
      | primary_expression, { ".", identifier }
      ;

  This slice exposes the outer named-vs-primary choice and the primary branch's
  projection-name spine.  The named_postfix_expression and primary_expression
  payloads remain exact certified ParseTree values for dedicated successor
  refinements.
*)

Definition phase1_surface_named_postfix_expression_node_tree
  (tree : ParseTree) : ParseTree := tree.

Definition phase1_surface_normalize_named_postfix_expression_node
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_validate_named_node "named_postfix_expression" tree with
  | Some tt => Some tree
  | None => None
  end.

Theorem phase1_surface_normalize_named_postfix_expression_node_round_trip :
  forall tree refined,
    phase1_surface_normalize_named_postfix_expression_node tree = Some refined ->
    phase1_surface_named_postfix_expression_node_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_named_postfix_expression_node in Hnormalize.
  destruct
    (phase1_surface_validate_named_node "named_postfix_expression" tree)
    as [[] |] eqn:Hvalidate; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  reflexivity.
Qed.

Definition phase1_surface_primary_expression_node_tree
  (tree : ParseTree) : ParseTree := tree.

Definition phase1_surface_normalize_primary_expression_node
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_validate_named_node "primary_expression" tree with
  | Some tt => Some tree
  | None => None
  end.

Theorem phase1_surface_normalize_primary_expression_node_round_trip :
  forall tree refined,
    phase1_surface_normalize_primary_expression_node tree = Some refined ->
    phase1_surface_primary_expression_node_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_primary_expression_node in Hnormalize.
  destruct
    (phase1_surface_validate_named_node "primary_expression" tree)
    as [[] |] eqn:Hvalidate; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  reflexivity.
Qed.

Inductive Phase1SurfacePostfixExpressionSpine : Type :=
| Phase1SurfacePostfixExpressionNamed
    (named : ParseTree)
| Phase1SurfacePostfixExpressionPrimary
    (primary : ParseTree)
    (projections : list string).

Definition phase1_surface_postfix_expression_spine_tree
  (expression : Phase1SurfacePostfixExpressionSpine) : ParseTree :=
  match expression with
  | Phase1SurfacePostfixExpressionNamed named =>
      PTNonterminal "postfix_expression"
        (PTAlternative 0
          (phase1_surface_named_postfix_expression_node_tree named))
  | Phase1SurfacePostfixExpressionPrimary primary projections =>
      PTNonterminal "postfix_expression"
        (PTAlternative 1
          (PTSequence
            [ phase1_surface_primary_expression_node_tree primary;
              PTRepetition
                (map (phase1_surface_name_suffix_tree ".") projections)
            ]))
  end.

Definition phase1_surface_normalize_postfix_expression_spine
  (tree : ParseTree) : option Phase1SurfacePostfixExpressionSpine :=
  match phase1_surface_expect_nonterminal "postfix_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_normalize_named_postfix_expression_node selected with
          | Some named => Some (Phase1SurfacePostfixExpressionNamed named)
          | None => None
          end
      | Some (1, selected) =>
          match phase1_surface_expect_sequence selected with
          | Some items =>
              match phase1_surface_exact2 items with
              | Some (primary_tree, projections_tree) =>
                  match phase1_surface_normalize_primary_expression_node primary_tree,
                        phase1_surface_expect_repetition projections_tree with
                  | Some primary, Some projection_trees =>
                      match
                        phase1_surface_normalize_name_suffixes
                          "." projection_trees
                      with
                      | Some projections =>
                          Some
                            (Phase1SurfacePostfixExpressionPrimary
                              primary projections)
                      | None => None
                      end
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_postfix_expression_spine_round_trip :
  forall tree expression,
    phase1_surface_normalize_postfix_expression_spine tree = Some expression ->
    phase1_surface_postfix_expression_spine_tree expression = tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_postfix_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "postfix_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_normalize_named_postfix_expression_node selected)
      as [named |] eqn:Hnamed; try discriminate Hnormalize.
    inversion Hnormalize; subst expression.
    unfold phase1_surface_postfix_expression_spine_tree.
    cbn.
    rewrite
      (phase1_surface_expect_nonterminal_round_trip
        "postfix_expression" tree body Hnode).
    rewrite
      (phase1_surface_expect_alternative_round_trip
        body 0 selected Halternative).
    rewrite
      (phase1_surface_normalize_named_postfix_expression_node_round_trip
        selected named Hnamed).
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_expect_sequence selected)
        as [items |] eqn:Hsequence; try discriminate Hnormalize.
      destruct (phase1_surface_exact2 items)
        as [[primary_tree projections_tree] |] eqn:Hitems;
        try discriminate Hnormalize.
      destruct (phase1_surface_normalize_primary_expression_node primary_tree)
        as [primary |] eqn:Hprimary; try discriminate Hnormalize.
      destruct (phase1_surface_expect_repetition projections_tree)
        as [projection_trees |] eqn:Hrepetition;
        try discriminate Hnormalize.
      destruct
        (phase1_surface_normalize_name_suffixes "." projection_trees)
        as [projections |] eqn:Hprojections;
        try discriminate Hnormalize.
      inversion Hnormalize; subst expression.
      unfold phase1_surface_postfix_expression_spine_tree.
      cbn.
      rewrite
        (phase1_surface_expect_nonterminal_round_trip
          "postfix_expression" tree body Hnode).
      rewrite
        (phase1_surface_expect_alternative_round_trip
          body 1 selected Halternative).
      rewrite
        (phase1_surface_expect_sequence_round_trip selected items Hsequence).
      rewrite
        (phase1_surface_exact2_round_trip
          items primary_tree projections_tree Hitems).
      rewrite
        (phase1_surface_normalize_primary_expression_node_round_trip
          primary_tree primary Hprimary).
      rewrite
        (phase1_surface_expect_repetition_round_trip
          projections_tree projection_trees Hrepetition).
      rewrite <-
        (phase1_surface_normalize_name_suffixes_round_trip
          "." projection_trees projections Hprojections).
      reflexivity.
    + discriminate Hnormalize.
Qed.
