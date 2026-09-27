From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionLiteralSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the char_literal payload retained by the primary-expression
  keyword-literal carrier:

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

  The char branch now exposes the CHAR_LITERAL lexical payload as a string.
  All other branches remain represented by the already-certified literal
  carrier. Runtime strings, floats, and integers stay exact ParseTree payloads
  for later focused lexical refinements.
*)

Inductive Phase1SurfacePrimaryExpressionCharSpine : Type :=
| Phase1PrimaryExpressionCharRefined
    (value : string)
| Phase1PrimaryExpressionCharPrior
    (expression : Phase1SurfacePrimaryExpressionLiteralSpine).

Definition phase1_surface_primary_expression_char_spine_tree
  (expression : Phase1SurfacePrimaryExpressionCharSpine) : ParseTree :=
  match expression with
  | Phase1PrimaryExpressionCharRefined value =>
      PTNonterminal "primary_expression"
        (PTAlternative 5
          (PTNonterminal "char_literal"
            (PTLexical "CHAR_LITERAL" value)))
  | Phase1PrimaryExpressionCharPrior prior =>
      phase1_surface_primary_expression_literal_spine_tree prior
  end.

Definition phase1_surface_normalize_primary_expression_char_spine
  (expression : Phase1SurfacePrimaryExpressionLiteralSpine)
  : option Phase1SurfacePrimaryExpressionCharSpine :=
  match expression with
  | Phase1PrimaryExpressionLexicalRetained 5 selected =>
      match phase1_surface_expect_nonterminal "char_literal" selected with
      | Some body =>
          match phase1_surface_expect_lexical "CHAR_LITERAL" body with
          | Some value =>
              Some (Phase1PrimaryExpressionCharRefined value)
          | None => None
          end
      | None => None
      end
  | _ => Some (Phase1PrimaryExpressionCharPrior expression)
  end.

Theorem
  phase1_surface_normalize_primary_expression_char_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_primary_expression_char_spine expression =
      Some refined ->
    phase1_surface_primary_expression_char_spine_tree refined =
      phase1_surface_primary_expression_literal_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as
    [tuple_expression
    | parenthesized
    |
    |
    |
    | branch selected].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
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
        -- inversion Hnormalize; subst refined.
           reflexivity.
        -- destruct branch as [|branch].
           ++ inversion Hnormalize; subst refined.
              reflexivity.
           ++ destruct branch as [|branch].
              ** inversion Hnormalize; subst refined.
                 reflexivity.
              ** destruct branch as [|branch].
                 --- cbn in Hnormalize.
                     destruct
                       (phase1_surface_expect_nonterminal
                         "char_literal" selected)
                       as [body |] eqn:Hnode;
                       try discriminate Hnormalize.
                     destruct
                       (phase1_surface_expect_lexical
                         "CHAR_LITERAL" body)
                       as [value |] eqn:Hlex;
                       try discriminate Hnormalize.
                     inversion Hnormalize; subst refined.
                     cbn.
                     rewrite
                       (phase1_surface_expect_nonterminal_round_trip
                         "char_literal" selected body Hnode).
                     rewrite
                       (phase1_surface_expect_lexical_round_trip
                         "CHAR_LITERAL" body value Hlex).
                     reflexivity.
                 --- inversion Hnormalize; subst refined.
                     reflexivity.
Qed.

Definition phase1_surface_normalize_primary_expression_char_tree
  (tree : ParseTree)
  : option Phase1SurfacePrimaryExpressionCharSpine :=
  match phase1_surface_normalize_primary_expression_literal_tree tree with
  | Some expression =>
      phase1_surface_normalize_primary_expression_char_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_primary_expression_char_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_primary_expression_char_tree tree =
      Some refined ->
    phase1_surface_primary_expression_char_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_primary_expression_char_tree in Hnormalize.
  destruct (phase1_surface_normalize_primary_expression_literal_tree tree)
    as [expression |] eqn:Hexpression;
    try discriminate Hnormalize.
  transitivity
    (phase1_surface_primary_expression_literal_spine_tree expression).
  - eapply
      phase1_surface_normalize_primary_expression_char_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_primary_expression_literal_tree_round_trip.
    exact Hexpression.
Qed.
