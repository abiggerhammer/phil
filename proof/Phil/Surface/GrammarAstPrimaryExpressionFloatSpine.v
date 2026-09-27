From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionStringSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the float_literal payload retained by the primary-expression
  runtime-string carrier:

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

  The float branch now exposes the DECIMAL_FLOAT lexical payload as a string.
  All previously refined grouping, keyword, char, and runtime-string branches
  remain represented by the already-certified string carrier. Integer literals
  stay exact ParseTree payloads for the next focused lexical refinement.
*)

Inductive Phase1SurfacePrimaryExpressionFloatSpine : Type :=
| Phase1PrimaryExpressionFloatRefined
    (value : string)
| Phase1PrimaryExpressionFloatPrior
    (expression : Phase1SurfacePrimaryExpressionStringSpine).

Definition phase1_surface_primary_expression_float_spine_tree
  (expression : Phase1SurfacePrimaryExpressionFloatSpine) : ParseTree :=
  match expression with
  | Phase1PrimaryExpressionFloatRefined value =>
      PTNonterminal "primary_expression"
        (PTAlternative 7
          (PTNonterminal "float_literal"
            (PTLexical "DECIMAL_FLOAT" value)))
  | Phase1PrimaryExpressionFloatPrior prior =>
      phase1_surface_primary_expression_string_spine_tree prior
  end.

Definition phase1_surface_normalize_primary_expression_float_spine
  (expression : Phase1SurfacePrimaryExpressionStringSpine)
  : option Phase1SurfacePrimaryExpressionFloatSpine :=
  match expression with
  | Phase1PrimaryExpressionStringPrior
      (Phase1PrimaryExpressionCharPrior
        (Phase1PrimaryExpressionLexicalRetained branch selected)) =>
      if Nat.eqb branch 7 then
        match phase1_surface_expect_nonterminal "float_literal" selected with
        | Some body =>
            match phase1_surface_expect_lexical "DECIMAL_FLOAT" body with
            | Some value =>
                Some (Phase1PrimaryExpressionFloatRefined value)
            | None => None
            end
        | None => None
        end
      else Some (Phase1PrimaryExpressionFloatPrior expression)
  | _ => Some (Phase1PrimaryExpressionFloatPrior expression)
  end.

Theorem
  phase1_surface_normalize_primary_expression_float_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_primary_expression_float_spine expression =
      Some refined ->
    phase1_surface_primary_expression_float_spine_tree refined =
      phase1_surface_primary_expression_string_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [string_value | char].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - destruct char as [char_value | literal].
    + inversion Hnormalize; subst refined.
      reflexivity.
    + destruct literal as
        [tuple_expression
        | parenthesized
        |
        |
        |
        | branch selected].
      * inversion Hnormalize; subst refined.
        reflexivity.
      * inversion Hnormalize; subst refined.
        reflexivity.
      * inversion Hnormalize; subst refined.
        reflexivity.
      * inversion Hnormalize; subst refined.
        reflexivity.
      * inversion Hnormalize; subst refined.
        reflexivity.
      * cbn in Hnormalize.
        destruct (Nat.eqb branch 7) eqn:Hbranch.
        -- apply Nat.eqb_eq in Hbranch.
           subst branch.
           destruct
             (phase1_surface_expect_nonterminal "float_literal" selected)
             as [body |] eqn:Hnode;
             try discriminate Hnormalize.
           destruct
             (phase1_surface_expect_lexical "DECIMAL_FLOAT" body)
             as [value |] eqn:Hlex;
             try discriminate Hnormalize.
           inversion Hnormalize; subst refined.
           cbn.
           rewrite
             (phase1_surface_expect_nonterminal_round_trip
               "float_literal" selected body Hnode).
           rewrite
             (phase1_surface_expect_lexical_round_trip
               "DECIMAL_FLOAT" body value Hlex).
           reflexivity.
        -- inversion Hnormalize; subst refined.
           reflexivity.
Qed.

Definition phase1_surface_normalize_primary_expression_float_tree
  (tree : ParseTree)
  : option Phase1SurfacePrimaryExpressionFloatSpine :=
  match phase1_surface_normalize_primary_expression_string_tree tree with
  | Some expression =>
      phase1_surface_normalize_primary_expression_float_spine expression
  | None => None
  end.

Theorem phase1_surface_normalize_primary_expression_float_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_primary_expression_float_tree tree =
      Some refined ->
    phase1_surface_primary_expression_float_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_primary_expression_float_tree in Hnormalize.
  destruct (phase1_surface_normalize_primary_expression_string_tree tree)
    as [expression |] eqn:Hexpression;
    try discriminate Hnormalize.
  transitivity
    (phase1_surface_primary_expression_string_spine_tree expression).
  - eapply
      phase1_surface_normalize_primary_expression_float_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_primary_expression_string_tree_round_trip.
    exact Hexpression.
Qed.
