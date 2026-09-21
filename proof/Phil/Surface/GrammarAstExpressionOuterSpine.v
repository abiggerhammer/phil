From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First Rocq refinement for ordinary runtime expression syntax.

  This slice opens only the outer expression shell:

    expression = base_expression, [ "or", fallback ] ;

  The base-expression precedence graph and fallback payload remain exact
  certified ParseTree values for dedicated successor refinements.
*)

Definition phase1_surface_expression_fallback_tail_tree
  (fallback : ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral "or";
      fallback
    ].

Definition phase1_surface_normalize_expression_fallback_tail
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (or_tree, fallback_tree) =>
          match phase1_surface_expect_literal "or" or_tree,
                phase1_surface_validate_named_node "fallback" fallback_tree with
          | Some tt, Some tt => Some fallback_tree
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_expression_fallback_tail_round_trip :
  forall tree fallback,
    phase1_surface_normalize_expression_fallback_tail tree = Some fallback ->
    phase1_surface_expression_fallback_tail_tree fallback = tree.
Proof.
  intros tree fallback Hnormalize.
  unfold phase1_surface_normalize_expression_fallback_tail in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[or_tree fallback_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "or" or_tree)
    as [[] |] eqn:Hor; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "fallback" fallback_tree)
    as [[] |] eqn:Hfallback; try discriminate Hnormalize.
  inversion Hnormalize; subst fallback.
  unfold phase1_surface_expression_fallback_tail_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items or_tree fallback_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "or" or_tree Hor).
  reflexivity.
Qed.

Definition phase1_surface_optional_expression_fallback_tree
  (fallback : option ParseTree) : ParseTree :=
  match fallback with
  | None => PTOptionalNone
  | Some fallback_value =>
      PTOptionalSome
        (phase1_surface_expression_fallback_tail_tree fallback_value)
  end.

Definition phase1_surface_normalize_optional_expression_fallback
  (tree : ParseTree) : option (option ParseTree) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_normalize_expression_fallback_tail body with
      | Some fallback => Some (Some fallback)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_expression_fallback_round_trip :
  forall tree fallback,
    phase1_surface_normalize_optional_expression_fallback tree = Some fallback ->
    phase1_surface_optional_expression_fallback_tree fallback = tree.
Proof.
  intros tree fallback Hnormalize.
  unfold phase1_surface_normalize_optional_expression_fallback in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_normalize_expression_fallback_tail body)
      as [actual |] eqn:Hfallback; try discriminate Hnormalize.
    inversion Hnormalize; subst fallback.
    unfold phase1_surface_optional_expression_fallback_tree.
    rewrite
      (phase1_surface_expect_optional_round_trip tree (Some body) Hoptional).
    rewrite
      (phase1_surface_normalize_expression_fallback_tail_round_trip
        body actual Hfallback).
    reflexivity.
  - inversion Hnormalize; subst fallback.
    unfold phase1_surface_optional_expression_fallback_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceExpressionOuterSpine : Type := {
  phase1_expression_outer_spine_base : ParseTree;
  phase1_expression_outer_spine_fallback : option ParseTree
}.

Definition phase1_surface_expression_outer_spine_tree
  (expression : Phase1SurfaceExpressionOuterSpine) : ParseTree :=
  PTNonterminal "expression"
    (PTSequence
      [ phase1_expression_outer_spine_base expression;
        phase1_surface_optional_expression_fallback_tree
          (phase1_expression_outer_spine_fallback expression)
      ]).

Definition phase1_surface_normalize_expression_outer_spine
  (tree : ParseTree) : option Phase1SurfaceExpressionOuterSpine :=
  match phase1_surface_expect_nonterminal "expression" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (base_tree, fallback_tree) =>
              match phase1_surface_validate_named_node
                      "base_expression" base_tree,
                    phase1_surface_normalize_optional_expression_fallback
                      fallback_tree with
              | Some tt, Some fallback =>
                  Some
                    {| phase1_expression_outer_spine_base := base_tree;
                       phase1_expression_outer_spine_fallback := fallback |}
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_expression_outer_spine_round_trip :
  forall tree expression,
    phase1_surface_normalize_expression_outer_spine tree = Some expression ->
    phase1_surface_expression_outer_spine_tree expression = tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_expression_outer_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[base_tree fallback_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "base_expression" base_tree)
    as [[] |] eqn:Hbase; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_optional_expression_fallback fallback_tree)
    as [fallback |] eqn:Hfallback; try discriminate Hnormalize.
  inversion Hnormalize; subst expression.
  unfold phase1_surface_expression_outer_spine_tree.
  cbn.
  rewrite
    (phase1_surface_expect_nonterminal_round_trip
      "expression" tree body Hnode).
  rewrite
    (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite
    (phase1_surface_exact2_round_trip
      items base_tree fallback_tree Hitems).
  rewrite
    (phase1_surface_normalize_optional_expression_fallback_round_trip
      fallback_tree fallback Hfallback).
  reflexivity.
Qed.
