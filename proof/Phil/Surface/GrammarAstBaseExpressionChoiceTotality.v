From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstBaseExpressionChoiceSpine
  GrammarAstExpressionOuterTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the base-expression choice shell from #1305. *)

Definition phase1_surface_base_expression_items_for_totality
  : list EbnfExpression :=
  [ ENonterminal "command_expression";
    ENonterminal "shift_expression"
  ].

Lemma phase1_surface_base_expression_lookup_for_totality :
  lookupRule "base_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_base_expression_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_normalize_base_expression_choice_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "base_expression")
      input rest tree ->
    exists expression,
      phase1_surface_normalize_base_expression_choice_spine tree =
        Some expression /\
      phase1_surface_base_expression_choice_spine_tree expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "base_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_base_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "base_expression"))
      phase1_surface_base_expression_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "command_expression" _ _ _ selected Hselected)
      as Hvalidate.
    assert (Hnormalize :
      phase1_surface_normalize_base_expression_choice_spine tree =
        Some (Phase1BaseExpressionCommand selected)).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_base_expression_choice_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hvalidate.
      reflexivity.
    }
    exists (Phase1BaseExpressionCommand selected).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_base_expression_choice_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "shift_expression" _ _ _ selected Hselected)
        as Hvalidate.
      assert (Hnormalize :
        phase1_surface_normalize_base_expression_choice_spine tree =
          Some (Phase1BaseExpressionShift selected)).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_base_expression_choice_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite Hvalidate.
        reflexivity.
      }
      exists (Phase1BaseExpressionShift selected).
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_base_expression_choice_spine_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
