From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstFallbackBaseChoiceSpine
  GrammarAstBaseExpressionChoiceTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the fallback base-choice shell from #1313. *)

Definition phase1_surface_fallback_items_for_totality
  : list EbnfExpression :=
  [ ESequence
      [ ELiteral "fail";
        ENonterminal "failure_target"
      ];
    ESequence
      [ ELiteral "reject";
        ENonterminal "base_expression"
      ]
  ].

Lemma phase1_surface_fallback_lookup_for_totality :
  lookupRule "fallback" phase1_surface_rules =
    Some (EAlternative phase1_surface_fallback_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_normalize_fallback_base_choice_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "fallback")
      input rest tree ->
    exists fallback,
      phase1_surface_normalize_fallback_base_choice_spine tree =
        Some fallback /\
      phase1_surface_fallback_base_choice_spine_tree fallback = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "fallback"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_fallback_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "fallback"))
      phase1_surface_fallback_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules _
        [ ELiteral "fail";
          ENonterminal "failure_target"
        ]
        input rest selected Hselected)
      as [trees [Hselected_tree Hitems]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules _ 0
        (ELiteral "fail")
        [ ENonterminal "failure_target" ]
        input rest trees Hitems)
      as [after_keyword [keyword_tree [tail_trees
        [Htrees [Hkeyword Htail]]]]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules _ 1
        (ENonterminal "failure_target") []
        after_keyword rest tail_trees Htail)
      as [after_target [failure_target [nil_trees
        [Htail_trees [Htarget Hnil]]]]].
    rewrite Htrees, Htail_trees in Hselected_tree.
    inversion Hnil; subst nil_trees.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "fail" _ _ keyword_tree Hkeyword)
      as [keyword_tail [_ [_ Hkeyword_tree]]].
    pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "failure_target" _ _ _ failure_target Htarget)
      as Htarget_validate.
    assert (Hnormalize :
      phase1_surface_normalize_fallback_base_choice_spine tree =
        Some (Phase1FallbackBaseChoiceFail failure_target)).
    {
      rewrite Htree, Hsubtree, Hselected_tree, Hkeyword_tree.
      unfold phase1_surface_normalize_fallback_base_choice_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_expect_literal.
      cbn.
      rewrite Htarget_validate.
      reflexivity.
    }
    exists (Phase1FallbackBaseChoiceFail failure_target).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_fallback_base_choice_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (derives_sequence_expression_exposes_items
          phase1_surface_rules _
          [ ELiteral "reject";
            ENonterminal "base_expression"
          ]
          input rest selected Hselected)
        as [trees [Hselected_tree Hitems]].
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 0
          (ELiteral "reject")
          [ ENonterminal "base_expression" ]
          input rest trees Hitems)
        as [after_keyword [keyword_tree [tail_trees
          [Htrees [Hkeyword Htail]]]]].
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 1
          (ENonterminal "base_expression") []
          after_keyword rest tail_trees Htail)
        as [after_base [base_tree [nil_trees
          [Htail_trees [Hbase Hnil]]]]].
      rewrite Htrees, Htail_trees in Hselected_tree.
      inversion Hnil; subst nil_trees.
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "reject" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]].
      destruct
        (phase1_surface_normalize_base_expression_choice_spine_total_from_derivation
          _ _ _ base_tree Hbase)
        as [base [Hbase_normalize Hbase_round_trip]].
      assert (Hnormalize :
        phase1_surface_normalize_fallback_base_choice_spine tree =
          Some (Phase1FallbackBaseChoiceReject base)).
      {
        rewrite Htree, Hsubtree, Hselected_tree, Hkeyword_tree.
        unfold phase1_surface_normalize_fallback_base_choice_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_literal.
        cbn.
        rewrite Hbase_normalize.
        reflexivity.
      }
      exists (Phase1FallbackBaseChoiceReject base).
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_fallback_base_choice_spine_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
