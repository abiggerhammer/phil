From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPostfixExpressionSpineTotality
  GrammarAstSourceHeader.

Import ListNotations.
Open Scope string_scope.

(*
  Open the named-postfix-expression boundary retained beneath the
  postfix-expression refinement chain:

    named_postfix_expression =
      qualified_name,
      [ static_arguments, [ term_arguments ], { ".", identifier }
        | term_arguments, { ".", identifier } ] ;

  This focused slice refines the qualified-name prefix and the presence or
  absence of the postfix tail.  The tail body itself remains an exact certified
  ParseTree for a dedicated successor refinement of its static-vs-term choice.
*)

Record Phase1SurfaceNamedPostfixExpressionSpine : Type := {
  phase1_named_postfix_expression_spine_name : Phase1SurfaceNameList;
  phase1_named_postfix_expression_spine_tail : option ParseTree
}.

Definition phase1_surface_named_postfix_expression_tail_tree
  (tail : option ParseTree) : ParseTree :=
  match tail with
  | None => PTOptionalNone
  | Some tail_tree => PTOptionalSome tail_tree
  end.

Definition phase1_surface_named_postfix_expression_spine_tree
  (expression : Phase1SurfaceNamedPostfixExpressionSpine) : ParseTree :=
  PTNonterminal "named_postfix_expression"
    (PTSequence
      [ phase1_surface_qualified_name_tree
          (phase1_named_postfix_expression_spine_name expression);
        phase1_surface_named_postfix_expression_tail_tree
          (phase1_named_postfix_expression_spine_tail expression)
      ]).

Definition phase1_surface_normalize_named_postfix_expression_spine
  (tree : ParseTree) : option Phase1SurfaceNamedPostfixExpressionSpine :=
  match phase1_surface_expect_nonterminal "named_postfix_expression" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (name_tree, tail_tree) =>
              match
                phase1_surface_normalize_qualified_name name_tree,
                phase1_surface_expect_optional tail_tree
              with
              | Some name, Some tail =>
                  Some
                    {| phase1_named_postfix_expression_spine_name := name;
                       phase1_named_postfix_expression_spine_tail := tail |}
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_named_postfix_expression_spine_round_trip :
  forall tree expression,
    phase1_surface_normalize_named_postfix_expression_spine tree =
      Some expression ->
    phase1_surface_named_postfix_expression_spine_tree expression = tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_named_postfix_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "named_postfix_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[name_tree tail_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_qualified_name name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_expect_optional tail_tree)
    as [[tail |] |] eqn:Htail; try discriminate Hnormalize.
  - inversion Hnormalize; subst expression.
    unfold phase1_surface_named_postfix_expression_spine_tree.
    cbn.
    rewrite
      (phase1_surface_expect_nonterminal_round_trip
        "named_postfix_expression" tree body Hnode).
    rewrite
      (phase1_surface_expect_sequence_round_trip body items Hsequence).
    rewrite
      (phase1_surface_exact2_round_trip
        items name_tree tail_tree Hitems).
    rewrite
      (phase1_surface_normalize_name_list_round_trip
        "qualified_name" "." name_tree name Hname).
    rewrite
      (phase1_surface_expect_optional_round_trip
        tail_tree (Some tail) Htail).
    reflexivity.
  - inversion Hnormalize; subst expression.
    unfold phase1_surface_named_postfix_expression_spine_tree.
    cbn.
    rewrite
      (phase1_surface_expect_nonterminal_round_trip
        "named_postfix_expression" tree body Hnode).
    rewrite
      (phase1_surface_expect_sequence_round_trip body items Hsequence).
    rewrite
      (phase1_surface_exact2_round_trip
        items name_tree tail_tree Hitems).
    rewrite
      (phase1_surface_normalize_name_list_round_trip
        "qualified_name" "." name_tree name Hname).
    rewrite
      (phase1_surface_expect_optional_round_trip tail_tree None Htail).
    reflexivity.
Qed.
