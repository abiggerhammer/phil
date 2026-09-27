From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstParenthesizedExpressionSpineTotality
  GrammarAstRefinementTupleTypePayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Open the tuple-expression payload retained by the primary-expression spine:

    tuple_expression =
      "(", expression, ",", expression, { ",", expression }, ")" ;

  This focused slice validates the exact tuple shell and every repeated
  comma-expression suffix while retaining each nested expression ParseTree for
  later recursive expression-layer refinement.
*)

Definition phase1_surface_tuple_expression_suffix_tree
  (expression_tree : ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      expression_tree
    ].

Definition phase1_surface_normalize_tuple_expression_suffix
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (comma_tree, expression_tree) =>
          match phase1_surface_expect_literal "," comma_tree,
                phase1_surface_validate_named_node
                  "expression" expression_tree with
          | Some tt, Some tt => Some expression_tree
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_tuple_expression_suffix_round_trip :
  forall tree expression_tree,
    phase1_surface_normalize_tuple_expression_suffix tree =
      Some expression_tree ->
    phase1_surface_tuple_expression_suffix_tree expression_tree = tree.
Proof.
  intros tree expression_tree Hnormalize.
  unfold phase1_surface_normalize_tuple_expression_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[comma_tree actual_expression_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node
      "expression" actual_expression_tree)
    as [[] |] eqn:Hexpression; try discriminate Hnormalize.
  inversion Hnormalize; subst expression_tree.
  unfold phase1_surface_tuple_expression_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite
    (phase1_surface_exact2_round_trip
      items comma_tree actual_expression_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_tuple_expression_suffixes
  (trees : list ParseTree) : option (list ParseTree) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_tuple_expression_suffix tree,
            phase1_surface_normalize_tuple_expression_suffixes rest with
      | Some expression_tree, Some expressions =>
          Some (expression_tree :: expressions)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_tuple_expression_suffixes_round_trip :
  forall trees expressions,
    phase1_surface_normalize_tuple_expression_suffixes trees =
      Some expressions ->
    map phase1_surface_tuple_expression_suffix_tree expressions = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros expressions Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst expressions.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_tuple_expression_suffix tree)
      as [expression_tree |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_tuple_expression_suffixes rest)
      as [rest_expressions |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst expressions.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_tuple_expression_suffix_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceTupleExpressionSpine : Type := {
  phase1_tuple_expression_spine_first : ParseTree;
  phase1_tuple_expression_spine_second : ParseTree;
  phase1_tuple_expression_spine_rest : list ParseTree
}.

Definition phase1_surface_tuple_expression_spine_tree
  (tuple_expression : Phase1SurfaceTupleExpressionSpine) : ParseTree :=
  PTNonterminal "tuple_expression"
    (PTSequence
      [ PTLiteral "(";
        phase1_tuple_expression_spine_first tuple_expression;
        PTLiteral ",";
        phase1_tuple_expression_spine_second tuple_expression;
        PTRepetition
          (map phase1_surface_tuple_expression_suffix_tree
            (phase1_tuple_expression_spine_rest tuple_expression));
        PTLiteral ")"
      ]).

Definition phase1_surface_normalize_tuple_expression_spine
  (tree : ParseTree) : option Phase1SurfaceTupleExpressionSpine :=
  match phase1_surface_expect_nonterminal "tuple_expression" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact6 items with
          | Some
              (open_tree, first_tree, comma_tree, second_tree,
               rest_tree, close_tree) =>
              match
                phase1_surface_expect_literal "(" open_tree,
                phase1_surface_validate_named_node "expression" first_tree,
                phase1_surface_expect_literal "," comma_tree,
                phase1_surface_validate_named_node "expression" second_tree,
                phase1_surface_expect_repetition rest_tree,
                phase1_surface_expect_literal ")" close_tree
              with
              | Some tt, Some tt, Some tt, Some tt,
                Some rest_trees, Some tt =>
                  match
                    phase1_surface_normalize_tuple_expression_suffixes
                      rest_trees
                  with
                  | Some rest =>
                      Some
                        {| phase1_tuple_expression_spine_first := first_tree;
                           phase1_tuple_expression_spine_second := second_tree;
                           phase1_tuple_expression_spine_rest := rest |}
                  | None => None
                  end
              | _, _, _, _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_tuple_expression_spine_round_trip :
  forall tree tuple_expression,
    phase1_surface_normalize_tuple_expression_spine tree =
      Some tuple_expression ->
    phase1_surface_tuple_expression_spine_tree tuple_expression = tree.
Proof.
  intros tree tuple_expression Hnormalize.
  unfold phase1_surface_normalize_tuple_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "tuple_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact6 items)
    as [[[[[[open_tree first_tree] comma_tree] second_tree]
           rest_tree] close_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node "expression" first_tree)
    as [[] |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node "expression" second_tree)
    as [[] |] eqn:Hsecond; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrest_trees; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_tuple_expression_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst tuple_expression.
  unfold phase1_surface_tuple_expression_spine_tree.
  rewrite
    (phase1_surface_expect_nonterminal_round_trip
      "tuple_expression" tree body Hnode).
  rewrite
    (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite
    (phase1_surface_exact6_round_trip
      items open_tree first_tree comma_tree second_tree rest_tree close_tree
      Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "(" open_tree Hopen).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  rewrite
    (phase1_surface_expect_repetition_round_trip
      rest_tree rest_trees Hrest_trees).
  rewrite
    (phase1_surface_normalize_tuple_expression_suffixes_round_trip
      rest_trees rest Hrest).
  rewrite (phase1_surface_expect_literal_round_trip ")" close_tree Hclose).
  reflexivity.
Qed.
