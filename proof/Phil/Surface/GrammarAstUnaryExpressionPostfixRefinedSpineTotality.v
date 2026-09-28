From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstUnaryExpressionPostfixRefinedSpine
  GrammarAstUnaryExpressionSpineTotality
  GrammarAstPostfixExpressionRefinedSpineTotality.

Import ListNotations.
Open Scope string_scope.

Theorem
  phase1_surface_normalize_unary_expression_postfix_refined_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "unary_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_unary_expression_postfix_refined_tree tree =
        Some refined /\
      phase1_surface_unary_expression_postfix_refined_spine_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "unary_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_unary_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "unary_expression"))
      phase1_surface_unary_expression_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules _
        [ ELiteral "-"; ENonterminal "unary_expression" ]
        input rest selected Hselected)
      as [trees [Hselected_tree Hitems]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules _ 0 (ELiteral "-")
        [ ENonterminal "unary_expression" ]
        input rest trees Hitems)
      as [after_minus [minus_tree [tail_trees
        [Htrees [Hminus Htail]]]]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules _ 1
        (ENonterminal "unary_expression") []
        after_minus rest tail_trees Htail)
      as [after_operand [operand_tree [nil_trees
        [Htail_trees [Hoperand Hnil]]]]].
    rewrite Htrees, Htail_trees in Hselected_tree.
    inversion Hnil; subst nil_trees.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "-" _ _ minus_tree Hminus)
      as [minus_tail [_ [_ Hminus_tree]]].
    pose proof
      (phase1_surface_normalize_unary_expression_node_total_from_derivation
        _ _ _ operand_tree Hoperand) as Hoperand_normalize.
    assert (Hspine :
      phase1_surface_normalize_unary_expression_spine tree =
        Some (Phase1SurfaceUnaryExpressionNegate operand_tree)).
    {
      rewrite Htree, Hsubtree, Hselected_tree, Hminus_tree.
      unfold phase1_surface_normalize_unary_expression_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_expect_literal.
      cbn.
      rewrite Hoperand_normalize.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_unary_expression_postfix_refined_tree tree =
        Some (Phase1SurfaceUnaryExpressionNegateRetained operand_tree)).
    {
      unfold phase1_surface_normalize_unary_expression_postfix_refined_tree.
      rewrite Hspine.
      reflexivity.
    }
    exists (Phase1SurfaceUnaryExpressionNegateRetained operand_tree).
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_unary_expression_postfix_refined_tree_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      pose proof
        (phase1_surface_normalize_postfix_expression_node_total_from_derivation
          _ _ _ selected Hselected) as Hpostfix_node.
      destruct
        (phase1_surface_normalize_postfix_expression_refined_tree_total_from_derivation
          _ _ _ selected Hselected)
        as [postfix [Hpostfix Hpostfix_round_trip]].
      assert (Hspine :
        phase1_surface_normalize_unary_expression_spine tree =
          Some (Phase1SurfaceUnaryExpressionPostfix selected)).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_unary_expression_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite Hpostfix_node.
        reflexivity.
      }
      assert (Hnormalize :
        phase1_surface_normalize_unary_expression_postfix_refined_tree tree =
          Some (Phase1SurfaceUnaryExpressionPostfixRefined postfix)).
      {
        unfold phase1_surface_normalize_unary_expression_postfix_refined_tree.
        rewrite Hspine.
        cbn.
        rewrite Hpostfix.
        reflexivity.
      }
      exists (Phase1SurfaceUnaryExpressionPostfixRefined postfix).
      split.
      * exact Hnormalize.
      * eapply
          phase1_surface_normalize_unary_expression_postfix_refined_tree_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
