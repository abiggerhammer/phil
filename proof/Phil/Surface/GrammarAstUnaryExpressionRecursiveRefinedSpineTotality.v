From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstUnaryExpressionRecursiveRefinedSpine
  GrammarAstUnaryExpressionPostfixRefinedSpineTotality.

Import ListNotations.
Open Scope string_scope.

Theorem
  phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "unary_expression")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_unary_expression_recursive_refined_spine_tree refined =
        tree.
Proof.
  fix IH 2.
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
      as [minus_tail [Hminus_input [Hminus_rest Hminus_tree]]].
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
    assert (Houter :
      phase1_surface_normalize_unary_expression_postfix_refined_tree tree =
        Some (Phase1SurfaceUnaryExpressionNegateRetained operand_tree)).
    {
      unfold phase1_surface_normalize_unary_expression_postfix_refined_tree.
      rewrite Hspine.
      reflexivity.
    }
    destruct input as [|token input_tail].
    + discriminate Hminus_input.
    + inversion Hminus_input; subst token minus_tail.
      subst after_minus.
      destruct (IH _ input_tail _ operand_tree Hoperand)
        as [fuel [refined_operand [Hrecursive Hrecursive_tree]]].
      assert (Hresult :
        phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
          (S fuel) tree =
        Some
          (Phase1SurfaceUnaryExpressionNegateRecursiveRefined
            refined_operand)).
      {
        unfold
          phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
          in Hrecursive |- *.
        rewrite Houter.
        cbn.
        destruct
          (phase1_surface_normalize_unary_expression_postfix_refined_tree
            operand_tree)
          as [operand |] eqn:Hoperand_refined.
        - cbn in Hrecursive |- *.
          rewrite Hrecursive.
          reflexivity.
        - discriminate Hrecursive.
      }
      exists (S fuel),
        (Phase1SurfaceUnaryExpressionNegateRecursiveRefined refined_operand).
      split.
      * exact Hresult.
      * eapply
          phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_round_trip.
        exact Hresult.
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
      assert (Houter :
        phase1_surface_normalize_unary_expression_postfix_refined_tree tree =
          Some (Phase1SurfaceUnaryExpressionPostfixRefined postfix)).
      {
        unfold phase1_surface_normalize_unary_expression_postfix_refined_tree.
        rewrite Hspine.
        cbn.
        rewrite Hpostfix.
        reflexivity.
      }
      assert (Hresult :
        phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel
          1 tree =
        Some
          (Phase1SurfaceUnaryExpressionPostfixRecursiveRefined postfix)).
      {
        unfold
          phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel.
        rewrite Houter.
        reflexivity.
      }
      exists 1,
        (Phase1SurfaceUnaryExpressionPostfixRecursiveRefined postfix).
      split.
      * exact Hresult.
      * eapply
          phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_round_trip.
        exact Hresult.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
