From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstBaseExpressionChoiceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Open the shift-expression precedence boundary retained by the
  fallback/base-choice refinement chain:

    shift_expression =
      additive_expression,
      { ( "<<" | ">>" ), additive_expression } ;

  This slice exposes only the shift shell and the exact left/right operator
  choice.  Each additive operand remains an exact certified ParseTree for a
  dedicated successor refinement.
*)

Inductive Phase1SurfaceShiftOperatorSpine : Type :=
| Phase1SurfaceShiftOperatorLeft
| Phase1SurfaceShiftOperatorRight.

Definition phase1_surface_shift_operator_spine_tree
  (operator : Phase1SurfaceShiftOperatorSpine) : ParseTree :=
  match operator with
  | Phase1SurfaceShiftOperatorLeft =>
      PTAlternative 0 (PTLiteral "<<")
  | Phase1SurfaceShiftOperatorRight =>
      PTAlternative 1 (PTLiteral ">>")
  end.

Definition phase1_surface_normalize_shift_operator_spine
  (tree : ParseTree) : option Phase1SurfaceShiftOperatorSpine :=
  match phase1_surface_expect_alternative tree with
  | Some (0, selected) =>
      match phase1_surface_expect_literal "<<" selected with
      | Some tt => Some Phase1SurfaceShiftOperatorLeft
      | None => None
      end
  | Some (1, selected) =>
      match phase1_surface_expect_literal ">>" selected with
      | Some tt => Some Phase1SurfaceShiftOperatorRight
      | None => None
      end
  | _ => None
  end.

Theorem phase1_surface_normalize_shift_operator_spine_round_trip :
  forall tree operator,
    phase1_surface_normalize_shift_operator_spine tree = Some operator ->
    phase1_surface_shift_operator_spine_tree operator = tree.
Proof.
  intros tree operator Hnormalize.
  unfold phase1_surface_normalize_shift_operator_spine in Hnormalize.
  destruct (phase1_surface_expect_alternative tree)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_expect_literal "<<" selected)
      as [[] |] eqn:Hleft; try discriminate Hnormalize.
    inversion Hnormalize; subst operator.
    unfold phase1_surface_shift_operator_spine_tree.
    rewrite
      (phase1_surface_expect_alternative_round_trip
        tree 0 selected Halternative).
    rewrite
      (phase1_surface_expect_literal_round_trip
        "<<" selected Hleft).
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_expect_literal ">>" selected)
        as [[] |] eqn:Hright; try discriminate Hnormalize.
      inversion Hnormalize; subst operator.
      unfold phase1_surface_shift_operator_spine_tree.
      rewrite
        (phase1_surface_expect_alternative_round_trip
          tree 1 selected Halternative).
      rewrite
        (phase1_surface_expect_literal_round_trip
          ">>" selected Hright).
      reflexivity.
    + discriminate Hnormalize.
Qed.

Definition phase1_surface_additive_expression_node_tree
  (tree : ParseTree) : ParseTree := tree.

Definition phase1_surface_normalize_additive_expression_node
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_validate_named_node "additive_expression" tree with
  | Some tt => Some tree
  | None => None
  end.

Theorem phase1_surface_normalize_additive_expression_node_round_trip :
  forall tree refined,
    phase1_surface_normalize_additive_expression_node tree = Some refined ->
    phase1_surface_additive_expression_node_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_additive_expression_node in Hnormalize.
  destruct
    (phase1_surface_validate_named_node "additive_expression" tree)
    as [[] |] eqn:Hvalidate; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  reflexivity.
Qed.

Record Phase1SurfaceShiftSuffixSpine : Type := {
  phase1_shift_suffix_spine_operator : Phase1SurfaceShiftOperatorSpine;
  phase1_shift_suffix_spine_right : ParseTree
}.

Definition phase1_surface_shift_suffix_spine_tree
  (suffix : Phase1SurfaceShiftSuffixSpine) : ParseTree :=
  PTSequence
    [ phase1_surface_shift_operator_spine_tree
        (phase1_shift_suffix_spine_operator suffix);
      phase1_surface_additive_expression_node_tree
        (phase1_shift_suffix_spine_right suffix)
    ].

Definition phase1_surface_normalize_shift_suffix_spine
  (tree : ParseTree) : option Phase1SurfaceShiftSuffixSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (operator_tree, right_tree) =>
          match phase1_surface_normalize_shift_operator_spine operator_tree,
                phase1_surface_normalize_additive_expression_node right_tree with
          | Some operator, Some right =>
              Some
                {| phase1_shift_suffix_spine_operator := operator;
                   phase1_shift_suffix_spine_right := right |}
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_shift_suffix_spine_round_trip :
  forall tree suffix,
    phase1_surface_normalize_shift_suffix_spine tree = Some suffix ->
    phase1_surface_shift_suffix_spine_tree suffix = tree.
Proof.
  intros tree suffix Hnormalize.
  unfold phase1_surface_normalize_shift_suffix_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[operator_tree right_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_shift_operator_spine operator_tree)
    as [operator |] eqn:Hoperator; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_additive_expression_node right_tree)
    as [right |] eqn:Hright; try discriminate Hnormalize.
  inversion Hnormalize; subst suffix.
  unfold phase1_surface_shift_suffix_spine_tree.
  cbn.
  rewrite
    (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite
    (phase1_surface_exact2_round_trip
      items operator_tree right_tree Hitems).
  rewrite
    (phase1_surface_normalize_shift_operator_spine_round_trip
      operator_tree operator Hoperator).
  rewrite
    (phase1_surface_normalize_additive_expression_node_round_trip
      right_tree right Hright).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_shift_suffix_spines
  (trees : list ParseTree) : option (list Phase1SurfaceShiftSuffixSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_shift_suffix_spine tree,
            phase1_surface_normalize_shift_suffix_spines rest with
      | Some suffix, Some suffixes => Some (suffix :: suffixes)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_shift_suffix_spines_round_trip :
  forall trees suffixes,
    phase1_surface_normalize_shift_suffix_spines trees = Some suffixes ->
    map phase1_surface_shift_suffix_spine_tree suffixes = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros suffixes Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst suffixes.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_shift_suffix_spine tree)
      as [suffix |] eqn:Hsuffix; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_shift_suffix_spines rest)
      as [suffixes_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst suffixes.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_shift_suffix_spine_round_trip.
      exact Hsuffix.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceShiftExpressionSpine : Type := {
  phase1_shift_expression_spine_first : ParseTree;
  phase1_shift_expression_spine_rest : list Phase1SurfaceShiftSuffixSpine
}.

Definition phase1_surface_shift_expression_spine_tree
  (expression : Phase1SurfaceShiftExpressionSpine) : ParseTree :=
  PTNonterminal "shift_expression"
    (PTSequence
      [ phase1_surface_additive_expression_node_tree
          (phase1_shift_expression_spine_first expression);
        PTRepetition
          (map phase1_surface_shift_suffix_spine_tree
            (phase1_shift_expression_spine_rest expression))
      ]).

Definition phase1_surface_normalize_shift_expression_spine
  (tree : ParseTree) : option Phase1SurfaceShiftExpressionSpine :=
  match phase1_surface_expect_nonterminal "shift_expression" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (first_tree, rest_tree) =>
              match phase1_surface_normalize_additive_expression_node first_tree,
                    phase1_surface_expect_repetition rest_tree with
              | Some first, Some rest_trees =>
                  match phase1_surface_normalize_shift_suffix_spines rest_trees with
                  | Some rest =>
                      Some
                        {| phase1_shift_expression_spine_first := first;
                           phase1_shift_expression_spine_rest := rest |}
                  | None => None
                  end
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_shift_expression_spine_round_trip :
  forall tree expression,
    phase1_surface_normalize_shift_expression_spine tree = Some expression ->
    phase1_surface_shift_expression_spine_tree expression = tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_shift_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "shift_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[first_tree rest_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_additive_expression_node first_tree)
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_shift_suffix_spines rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst expression.
  unfold phase1_surface_shift_expression_spine_tree.
  cbn.
  rewrite
    (phase1_surface_expect_nonterminal_round_trip
      "shift_expression" tree body Hnode).
  rewrite
    (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite
    (phase1_surface_exact2_round_trip
      items first_tree rest_tree Hitems).
  rewrite
    (phase1_surface_normalize_additive_expression_node_round_trip
      first_tree first Hfirst).
  rewrite
    (phase1_surface_expect_repetition_round_trip
      rest_tree rest_trees Hrepetition).
  rewrite <-
    (phase1_surface_normalize_shift_suffix_spines_round_trip
      rest_trees rest Hrest).
  reflexivity.
Qed.
