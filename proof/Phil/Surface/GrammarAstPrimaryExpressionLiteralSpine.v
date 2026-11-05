From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the three closed keyword-literal branches retained by the
  primary-expression grouping carrier:

    primary_expression =
        tuple_expression
      | parenthesized_expression
      | "true"
      | "false"
      | "unit"
      | char_literal
      | runtime_string_literal
      | float_literal
      | integer_literal
      ;

  The grouping branches remain structurally refined. The boolean and unit
  branches become explicit constructors, while char/string/float/integer
  payloads remain exact certified ParseTree values for later lexical slices.
*)

Inductive Phase1SurfacePrimaryExpressionLiteralSpine : Type :=
| Phase1PrimaryExpressionLiteralTuple
    (tuple_expression : Phase1SurfaceTupleExpressionSpine)
| Phase1PrimaryExpressionLiteralParenthesized
    (parenthesized : Phase1SurfaceParenthesizedExpressionSpine)
| Phase1PrimaryExpressionTrue
| Phase1PrimaryExpressionFalse
| Phase1PrimaryExpressionUnit
| Phase1PrimaryExpressionLexicalRetained
    (branch : nat)
    (selected : ParseTree).

Definition phase1_surface_primary_expression_literal_spine_tree
  (expression : Phase1SurfacePrimaryExpressionLiteralSpine) : ParseTree :=
  match expression with
  | Phase1PrimaryExpressionLiteralTuple tuple_expression =>
      PTNonterminal "primary_expression"
        (PTAlternative 0
          (phase1_surface_tuple_expression_spine_tree tuple_expression))
  | Phase1PrimaryExpressionLiteralParenthesized parenthesized =>
      PTNonterminal "primary_expression"
        (PTAlternative 1
          (phase1_surface_parenthesized_expression_spine_tree parenthesized))
  | Phase1PrimaryExpressionTrue =>
      PTNonterminal "primary_expression" (PTAlternative 2 (PTLiteral "true"))
  | Phase1PrimaryExpressionFalse =>
      PTNonterminal "primary_expression" (PTAlternative 3 (PTLiteral "false"))
  | Phase1PrimaryExpressionUnit =>
      PTNonterminal "primary_expression" (PTAlternative 4 (PTLiteral "unit"))
  | Phase1PrimaryExpressionLexicalRetained branch selected =>
      PTNonterminal "primary_expression" (PTAlternative branch selected)
  end.

Definition phase1_surface_normalize_primary_expression_literal_spine
  (expression : Phase1SurfacePrimaryExpressionGroupingSpine)
  : option Phase1SurfacePrimaryExpressionLiteralSpine :=
  match expression with
  | Phase1PrimaryExpressionTupleRefined tuple_expression =>
      Some (Phase1PrimaryExpressionLiteralTuple tuple_expression)
  | Phase1PrimaryExpressionParenthesizedRefined parenthesized =>
      Some (Phase1PrimaryExpressionLiteralParenthesized parenthesized)
  | Phase1PrimaryExpressionOtherRetained branch selected =>
      match branch with
      | 2 =>
          match phase1_surface_expect_literal "true" selected with
          | Some tt => Some Phase1PrimaryExpressionTrue
          | None => None
          end
      | 3 =>
          match phase1_surface_expect_literal "false" selected with
          | Some tt => Some Phase1PrimaryExpressionFalse
          | None => None
          end
      | 4 =>
          match phase1_surface_expect_literal "unit" selected with
          | Some tt => Some Phase1PrimaryExpressionUnit
          | None => None
          end
      | _ =>
          Some (Phase1PrimaryExpressionLexicalRetained branch selected)
      end
  end.

Theorem
  phase1_surface_normalize_primary_expression_literal_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_primary_expression_literal_spine expression =
      Some refined ->
    phase1_surface_primary_expression_literal_spine_tree refined =
      phase1_surface_primary_expression_grouping_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [tuple_expression | parenthesized | branch selected].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
  - destruct branch as [|branch].
    + inversion Hnormalize; subst refined.
      reflexivity.
    + destruct branch as [|branch].
      * inversion Hnormalize; subst refined.
        reflexivity.
      * destruct branch as [|branch].
        -- cbn in Hnormalize.
           destruct (phase1_surface_expect_literal "true" selected)
             as [[] |] eqn:Hliteral;
             try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           cbn.
           rewrite
             (phase1_surface_expect_literal_round_trip
               "true" selected Hliteral).
           reflexivity.
        -- destruct branch as [|branch].
           ++ cbn in Hnormalize.
              destruct (phase1_surface_expect_literal "false" selected)
                as [[] |] eqn:Hliteral;
                try discriminate Hnormalize.
              inversion Hnormalize; subst refined.
              cbn.
              rewrite
                (phase1_surface_expect_literal_round_trip
                  "false" selected Hliteral).
              reflexivity.
           ++ destruct branch as [|branch].
              ** cbn in Hnormalize.
                 destruct (phase1_surface_expect_literal "unit" selected)
                   as [[] |] eqn:Hliteral;
                   try discriminate Hnormalize.
                 inversion Hnormalize; subst refined.
                 cbn.
                 rewrite
                   (phase1_surface_expect_literal_round_trip
                     "unit" selected Hliteral).
                 reflexivity.
              ** inversion Hnormalize; subst refined.
                 reflexivity.
Qed.

Definition phase1_surface_normalize_primary_expression_literal_tree
  (tree : ParseTree)
  : option Phase1SurfacePrimaryExpressionLiteralSpine :=
  match phase1_surface_normalize_primary_expression_grouping_tree tree with
  | Some expression =>
      phase1_surface_normalize_primary_expression_literal_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_primary_expression_literal_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_primary_expression_literal_tree tree =
      Some refined ->
    phase1_surface_primary_expression_literal_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_primary_expression_literal_tree in Hnormalize.
  destruct (phase1_surface_normalize_primary_expression_grouping_tree tree)
    as [expression |] eqn:Hexpression;
    try discriminate Hnormalize.
  transitivity
    (phase1_surface_primary_expression_grouping_spine_tree expression).
  - eapply
      phase1_surface_normalize_primary_expression_literal_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_primary_expression_grouping_tree_round_trip.
    exact Hexpression.
Qed.
