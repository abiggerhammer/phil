From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionIntegerSpine
  GrammarAstPrimaryExpressionFloatSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the integer-literal refinement introduced by #1446.

  The integer spine exposes the final primary_expression lexical payload,
  DECIMAL_INTEGER, while preserving every earlier grouping, keyword, char,
  runtime-string, and float refinement. This companion proves totality on
  grammar-derived primary_expression trees and exact reconstruction.

  This remains structural only: integer decoding, canonicalization, range
  semantics, nested ordinary-expression semantics, and broader parser claims
  are outside this slice. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_integer_literal_lookup_for_primary_expression_totality :
  lookupRule "integer_literal" phase1_surface_rules =
    Some (ELexicalClass "DECIMAL_INTEGER").
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_primary_expression_integer_totality_lift :
  forall tree float_expression refined,
    phase1_surface_normalize_primary_expression_float_tree tree =
      Some float_expression ->
    phase1_surface_normalize_primary_expression_integer_spine float_expression =
      Some refined ->
    phase1_surface_normalize_primary_expression_integer_tree tree =
      Some refined /\
    phase1_surface_primary_expression_integer_spine_tree refined = tree.
Proof.
  intros tree float_expression refined Hfloat Hinteger.
  split.
  - unfold phase1_surface_normalize_primary_expression_integer_tree.
    rewrite Hfloat.
    exact Hinteger.
  - eapply phase1_surface_normalize_primary_expression_integer_tree_round_trip.
    unfold phase1_surface_normalize_primary_expression_integer_tree.
    rewrite Hfloat.
    exact Hinteger.
Qed.

Theorem
  phase1_surface_normalize_primary_expression_integer_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "primary_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_primary_expression_integer_tree tree =
        Some refined /\
      phase1_surface_primary_expression_integer_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_primary_expression_float_tree_total_from_derivation
      path input rest tree Hderive)
    as [float_expression [Hfloat Hfloat_tree]].
  destruct float_expression as [float_value | string_expression].
  - exists
      (Phase1PrimaryExpressionIntegerPrior
        (Phase1PrimaryExpressionFloatRefined float_value)).
    eapply phase1_surface_primary_expression_integer_totality_lift.
    + exact Hfloat.
    + reflexivity.
  - destruct string_expression as [string_value | char_expression].
    + exists
        (Phase1PrimaryExpressionIntegerPrior
          (Phase1PrimaryExpressionFloatPrior
            (Phase1PrimaryExpressionStringRefined string_value))).
      eapply phase1_surface_primary_expression_integer_totality_lift.
      * exact Hfloat.
      * reflexivity.
    + destruct char_expression as [char_value | literal_expression].
      * exists
          (Phase1PrimaryExpressionIntegerPrior
            (Phase1PrimaryExpressionFloatPrior
              (Phase1PrimaryExpressionStringPrior
                (Phase1PrimaryExpressionCharRefined char_value)))).
        eapply phase1_surface_primary_expression_integer_totality_lift.
        -- exact Hfloat.
        -- reflexivity.
      * destruct literal_expression as
          [tuple_expression | parenthesized | | | | branch selected].
        -- exists
             (Phase1PrimaryExpressionIntegerPrior
               (Phase1PrimaryExpressionFloatPrior
                 (Phase1PrimaryExpressionStringPrior
                   (Phase1PrimaryExpressionCharPrior
                     (Phase1PrimaryExpressionLiteralTuple tuple_expression))))).
           eapply phase1_surface_primary_expression_integer_totality_lift.
           ++ exact Hfloat.
           ++ reflexivity.
        -- exists
             (Phase1PrimaryExpressionIntegerPrior
               (Phase1PrimaryExpressionFloatPrior
                 (Phase1PrimaryExpressionStringPrior
                   (Phase1PrimaryExpressionCharPrior
                     (Phase1PrimaryExpressionLiteralParenthesized parenthesized))))).
           eapply phase1_surface_primary_expression_integer_totality_lift.
           ++ exact Hfloat.
           ++ reflexivity.
        -- exists
             (Phase1PrimaryExpressionIntegerPrior
               (Phase1PrimaryExpressionFloatPrior
                 (Phase1PrimaryExpressionStringPrior
                   (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionTrue)))).
           eapply phase1_surface_primary_expression_integer_totality_lift.
           ++ exact Hfloat.
           ++ reflexivity.
        -- exists
             (Phase1PrimaryExpressionIntegerPrior
               (Phase1PrimaryExpressionFloatPrior
                 (Phase1PrimaryExpressionStringPrior
                   (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionFalse)))).
           eapply phase1_surface_primary_expression_integer_totality_lift.
           ++ exact Hfloat.
           ++ reflexivity.
        -- exists
             (Phase1PrimaryExpressionIntegerPrior
               (Phase1PrimaryExpressionFloatPrior
                 (Phase1PrimaryExpressionStringPrior
                   (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionUnit)))).
           eapply phase1_surface_primary_expression_integer_totality_lift.
           ++ exact Hfloat.
           ++ reflexivity.
        -- destruct (Nat.eqb branch 8) eqn:Hbranch.
           ++ apply Nat.eqb_eq in Hbranch.
              subst branch.
              cbn in Hfloat_tree.
              rewrite <- Hfloat_tree in Hderive.
              destruct
                (derives_nonterminal_exposes_body
                  phase1_surface_rules path "primary_expression"
                  input rest
                  (PTNonterminal "primary_expression"
                    (PTAlternative 8 selected))
                  Hderive)
                as [body [subtree [Hlookup [Htree Hbody]]]].
              rewrite
                phase1_surface_primary_expression_lookup_for_totality
                in Hlookup.
              inversion Hlookup; subst body.
              inversion Htree; subst subtree.
              destruct
                (alternative_derivation_names_exact_branch
                  phase1_surface_rules
                  (descend path (AtNonterminal "primary_expression"))
                  phase1_surface_primary_expression_items_for_totality
                  input rest (PTAlternative 8 selected) Hbody)
                as
                  [index
                    [item
                      [chosen [Hnth [Halternative Hselected]]]]].
              inversion Halternative; subst index chosen.
              cbn in Hnth.
              inversion Hnth; subst item.
              destruct
                (derives_nonterminal_exposes_body
                  phase1_surface_rules _ "integer_literal"
                  _ _ selected Hselected)
                as
                  [integer_body
                    [lexical_tree
                      [Hinteger_lookup [Hinteger_tree Hlexical]]]].
              rewrite
                phase1_surface_integer_literal_lookup_for_primary_expression_totality
                in Hinteger_lookup.
              inversion Hinteger_lookup; subst integer_body.
              destruct
                (lexical_derivation_is_exact
                  phase1_surface_rules _ "DECIMAL_INTEGER"
                  _ _ lexical_tree Hlexical)
                as [value [tail [_ [_ Hlexical_tree]]]].
              exists (Phase1PrimaryExpressionIntegerRefined value).
              eapply phase1_surface_primary_expression_integer_totality_lift.
              ** exact Hfloat.
              ** cbn.
                 rewrite Hinteger_tree, Hlexical_tree.
                 unfold phase1_surface_expect_nonterminal,
                   phase1_surface_expect_lexical.
                 cbn.
                 repeat rewrite String.eqb_refl.
                 reflexivity.
           ++ exists
                (Phase1PrimaryExpressionIntegerPrior
                  (Phase1PrimaryExpressionFloatPrior
                    (Phase1PrimaryExpressionStringPrior
                      (Phase1PrimaryExpressionCharPrior
                        (Phase1PrimaryExpressionLexicalRetained
                          branch selected))))).
              eapply phase1_surface_primary_expression_integer_totality_lift.
              ** exact Hfloat.
              ** cbn.
                 rewrite Hbranch.
                 reflexivity.
Qed.
