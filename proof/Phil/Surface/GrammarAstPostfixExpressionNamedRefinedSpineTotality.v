From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPostfixExpressionNamedRefinedSpine
  GrammarAstPostfixExpressionSpineTotality
  GrammarAstNamedPostfixExpressionRefinedTailSpineTotality.

Import ListNotations.
Open Scope string_scope.

Theorem
  phase1_surface_normalize_postfix_expression_named_refined_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "postfix_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_postfix_expression_named_refined_tree tree =
        Some refined /\
      phase1_surface_postfix_expression_named_refined_spine_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "postfix_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_postfix_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "postfix_expression"))
      phase1_surface_postfix_expression_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    pose proof
      (phase1_surface_normalize_named_postfix_expression_node_total_from_derivation
        _ _ _ selected Hselected) as Hnamed_node.
    destruct
      (phase1_surface_normalize_named_postfix_expression_refined_tail_tree_total_from_derivation
        _ _ _ selected Hselected)
      as [named [Hnamed_refined Hnamed_round_trip]].
    assert (Hspine :
      phase1_surface_normalize_postfix_expression_spine tree =
        Some (Phase1SurfacePostfixExpressionNamed selected)).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_postfix_expression_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hnamed_node.
      reflexivity.
    }
    assert (Hrefined :
      phase1_surface_normalize_postfix_expression_named_refined_tree tree =
        Some (Phase1SurfacePostfixExpressionNamedRefined named)).
    {
      unfold phase1_surface_normalize_postfix_expression_named_refined_tree.
      rewrite Hspine.
      cbn.
      rewrite Hnamed_refined.
      reflexivity.
    }
    exists (Phase1SurfacePostfixExpressionNamedRefined named).
    split.
    + exact Hrefined.
    + eapply
        phase1_surface_normalize_postfix_expression_named_refined_tree_round_trip.
      exact Hrefined.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (derives_sequence_expression_exposes_items
          phase1_surface_rules _
          [ ENonterminal "primary_expression";
            ERepetition
              (ESequence [ELiteral "."; ENonterminal "identifier"])
          ]
          input rest selected Hselected)
        as [trees [Hselected_tree Hitems]].
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 0
          (ENonterminal "primary_expression")
          [ ERepetition
              (ESequence [ELiteral "."; ENonterminal "identifier"])
          ]
          input rest trees Hitems)
        as [after_primary [primary_tree [tail_trees
          [Htrees [Hprimary Htail]]]]].
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 1
          (ERepetition
            (ESequence [ELiteral "."; ENonterminal "identifier"])) []
          after_primary rest tail_trees Htail)
        as [after_projections [projections_tree [nil_trees
          [Htail_trees [Hprojections Hnil]]]]].
      rewrite Htrees, Htail_trees in Hselected_tree.
      inversion Hnil; subst nil_trees.
      pose proof
        (phase1_surface_normalize_primary_expression_node_total_from_derivation
          _ _ _ primary_tree Hprimary) as Hprimary_normalize.
      destruct
        (phase1_surface_repetition_derivation_exposes
          _
          (ESequence [ELiteral "."; ENonterminal "identifier"])
          _ _ projections_tree Hprojections)
        as [projection_trees [Hprojections_tree Hprojections_body]].
      destruct
        (phase1_surface_normalize_name_suffixes_total_from_repetition
          "." _
          (ESequence [ELiteral "."; ENonterminal "identifier"])
          _ _ projection_trees Hprojections_body eq_refl)
        as [projection_names Hprojection_names].
      assert (Hspine :
        phase1_surface_normalize_postfix_expression_spine tree =
          Some
            (Phase1SurfacePostfixExpressionPrimary
              primary_tree projection_names)).
      {
        rewrite Htree, Hsubtree, Hselected_tree, Hprojections_tree.
        unfold phase1_surface_normalize_postfix_expression_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_repetition.
        cbn.
        rewrite Hprimary_normalize, Hprojection_names.
        reflexivity.
      }
      assert (Hrefined :
        phase1_surface_normalize_postfix_expression_named_refined_tree tree =
          Some
            (Phase1SurfacePostfixExpressionPrimaryRetained
              primary_tree projection_names)).
      {
        unfold phase1_surface_normalize_postfix_expression_named_refined_tree.
        rewrite Hspine.
        reflexivity.
      }
      exists
        (Phase1SurfacePostfixExpressionPrimaryRetained
          primary_tree projection_names).
      split.
      * exact Hrefined.
      * eapply
          phase1_surface_normalize_postfix_expression_named_refined_tree_round_trip.
        exact Hrefined.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
