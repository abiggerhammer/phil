From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionCharSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the runtime_string_literal payload retained by the primary-expression
  char carrier:

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

  The runtime-string branch now exposes the STRING_LITERAL lexical payload as
  a string. All previously refined tuple, grouping, keyword, and char branches
  remain represented by the already-certified char carrier. Floats and
  integers stay exact ParseTree payloads for later focused lexical refinements.
*)

Inductive Phase1SurfacePrimaryExpressionStringSpine : Type :=
| Phase1PrimaryExpressionStringRefined
    (value : string)
| Phase1PrimaryExpressionStringPrior
    (expression : Phase1SurfacePrimaryExpressionCharSpine).

Definition phase1_surface_primary_expression_string_spine_tree
  (expression : Phase1SurfacePrimaryExpressionStringSpine) : ParseTree :=
  match expression with
  | Phase1PrimaryExpressionStringRefined value =>
      PTNonterminal "primary_expression"
        (PTAlternative 6
          (PTNonterminal "runtime_string_literal"
            (PTLexical "STRING_LITERAL" value)))
  | Phase1PrimaryExpressionStringPrior prior =>
      phase1_surface_primary_expression_char_spine_tree prior
  end.

Definition phase1_surface_normalize_primary_expression_string_spine
  (expression : Phase1SurfacePrimaryExpressionCharSpine)
  : option Phase1SurfacePrimaryExpressionStringSpine :=
  match expression with
  | Phase1PrimaryExpressionCharPrior
      (Phase1PrimaryExpressionLexicalRetained branch selected) =>
      if Nat.eqb branch 6 then
        match phase1_surface_expect_nonterminal "runtime_string_literal" selected with
        | Some body =>
            match phase1_surface_expect_lexical "STRING_LITERAL" body with
            | Some value =>
                Some (Phase1PrimaryExpressionStringRefined value)
            | None => None
            end
        | None => None
        end
      else Some (Phase1PrimaryExpressionStringPrior expression)
  | _ => Some (Phase1PrimaryExpressionStringPrior expression)
  end.

Theorem
  phase1_surface_normalize_primary_expression_string_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_primary_expression_string_spine expression =
      Some refined ->
    phase1_surface_primary_expression_string_spine_tree refined =
      phase1_surface_primary_expression_char_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [char_value | literal].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - destruct literal as
      [tuple_expression
      | parenthesized
      |
      |
      |
      | branch selected].
    + inversion Hnormalize; subst refined.
      reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
    + cbn in Hnormalize.
      destruct (Nat.eqb branch 6) eqn:Hbranch.
      * apply Nat.eqb_eq in Hbranch.
        subst branch.
        destruct
          (phase1_surface_expect_nonterminal
            "runtime_string_literal" selected)
          as [body |] eqn:Hnode;
          try discriminate Hnormalize.
        destruct
          (phase1_surface_expect_lexical
            "STRING_LITERAL" body)
          as [value |] eqn:Hlex;
          try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        cbn.
        rewrite
          (phase1_surface_expect_nonterminal_round_trip
            "runtime_string_literal" selected body Hnode).
        rewrite
          (phase1_surface_expect_lexical_round_trip
            "STRING_LITERAL" body value Hlex).
        reflexivity.
      * inversion Hnormalize; subst refined.
        reflexivity.
Qed.

Definition phase1_surface_normalize_primary_expression_string_tree
  (tree : ParseTree)
  : option Phase1SurfacePrimaryExpressionStringSpine :=
  match phase1_surface_normalize_primary_expression_char_tree tree with
  | Some expression =>
      phase1_surface_normalize_primary_expression_string_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_primary_expression_string_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_primary_expression_string_tree tree =
      Some refined ->
    phase1_surface_primary_expression_string_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_primary_expression_string_tree in Hnormalize.
  destruct (phase1_surface_normalize_primary_expression_char_tree tree)
    as [expression |] eqn:Hexpression;
    try discriminate Hnormalize.
  transitivity
    (phase1_surface_primary_expression_char_spine_tree expression).
  - eapply
      phase1_surface_normalize_primary_expression_string_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_primary_expression_char_tree_round_trip.
    exact Hexpression.
Qed.
