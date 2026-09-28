From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionFloatSpineTotality.

Import ListNotations.
Open Scope string_scope.

Inductive Phase1SurfacePrimaryExpressionIntegerSpine : Type :=
| Phase1PrimaryExpressionIntegerRefined (value : string)
| Phase1PrimaryExpressionIntegerPrior
    (expression : Phase1SurfacePrimaryExpressionFloatSpine).

Definition phase1_surface_primary_expression_integer_spine_tree
  (expression : Phase1SurfacePrimaryExpressionIntegerSpine) : ParseTree :=
  match expression with
  | Phase1PrimaryExpressionIntegerRefined value =>
      PTNonterminal "primary_expression"
        (PTAlternative 8
          (PTNonterminal "integer_literal"
            (PTLexical "DECIMAL_INTEGER" value)))
  | Phase1PrimaryExpressionIntegerPrior prior =>
      phase1_surface_primary_expression_float_spine_tree prior
  end.

Definition phase1_surface_normalize_primary_expression_integer_spine
  (expression : Phase1SurfacePrimaryExpressionFloatSpine)
  : option Phase1SurfacePrimaryExpressionIntegerSpine :=
  match expression with
  | Phase1PrimaryExpressionFloatPrior
      (Phase1PrimaryExpressionStringPrior
        (Phase1PrimaryExpressionCharPrior
          (Phase1PrimaryExpressionLexicalRetained branch selected))) =>
      if Nat.eqb branch 8 then
        match phase1_surface_expect_nonterminal "integer_literal" selected with
        | Some body =>
            match phase1_surface_expect_lexical "DECIMAL_INTEGER" body with
            | Some value => Some (Phase1PrimaryExpressionIntegerRefined value)
            | None => None
            end
        | None => None
        end
      else Some (Phase1PrimaryExpressionIntegerPrior expression)
  | _ => Some (Phase1PrimaryExpressionIntegerPrior expression)
  end.

Theorem
  phase1_surface_normalize_primary_expression_integer_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_primary_expression_integer_spine expression =
      Some refined ->
    phase1_surface_primary_expression_integer_spine_tree refined =
      phase1_surface_primary_expression_float_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [float_value | prior].
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct prior as [string_value | char].
    + inversion Hnormalize; subst refined. reflexivity.
    + destruct char as [char_value | literal].
      * inversion Hnormalize; subst refined. reflexivity.
      * destruct literal as
          [tuple_expression | parenthesized | | | | branch selected].
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- inversion Hnormalize; subst refined. reflexivity.
        -- cbn in Hnormalize.
           destruct (Nat.eqb branch 8) eqn:Hbranch.
           ++ apply Nat.eqb_eq in Hbranch. subst branch.
              destruct
                (phase1_surface_expect_nonterminal "integer_literal" selected)
                as [body |] eqn:Hnode;
                try discriminate Hnormalize.
              destruct
                (phase1_surface_expect_lexical "DECIMAL_INTEGER" body)
                as [value |] eqn:Hlex;
                try discriminate Hnormalize.
              inversion Hnormalize; subst refined.
              cbn.
              rewrite
                (phase1_surface_expect_nonterminal_round_trip
                  "integer_literal" selected body Hnode).
              rewrite
                (phase1_surface_expect_lexical_round_trip
                  "DECIMAL_INTEGER" body value Hlex).
              reflexivity.
           ++ inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_primary_expression_integer_tree
  (tree : ParseTree)
  : option Phase1SurfacePrimaryExpressionIntegerSpine :=
  match phase1_surface_normalize_primary_expression_float_tree tree with
  | Some expression =>
      phase1_surface_normalize_primary_expression_integer_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_primary_expression_integer_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_primary_expression_integer_tree tree =
      Some refined ->
    phase1_surface_primary_expression_integer_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_primary_expression_integer_tree in Hnormalize.
  destruct (phase1_surface_normalize_primary_expression_float_tree tree)
    as [expression |] eqn:Hexpression;
    try discriminate Hnormalize.
  transitivity
    (phase1_surface_primary_expression_float_spine_tree expression).
  - eapply phase1_surface_normalize_primary_expression_integer_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_primary_expression_float_tree_round_trip.
    exact Hexpression.
Qed.
