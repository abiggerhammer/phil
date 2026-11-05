From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionGroupingSpine
  GrammarAstPrimaryExpressionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the grouping refinement opened by #1435.

  The primary-expression grouping normalizer lifts the tuple_expression and
  parenthesized_expression branches into their dedicated structural carriers
  and retains every remaining primary_expression branch exactly. This
  companion proves that every derivable primary_expression tree is accepted by
  that refinement and reconstructed exactly.

  The result is intentionally structural: nested ordinary-expression payloads
  remain certified ParseTree values, and the remaining literal/lexical primary
  branches are still retained for later focused refinement.
*)

Lemma
  phase1_surface_normalize_primary_expression_grouping_spine_total_from_branch_derivation :
  forall index item path input rest selected,
    nth_error phase1_surface_primary_expression_items_for_totality index =
      Some item ->
    Derives phase1_surface_rules path item input rest selected ->
    exists refined,
      phase1_surface_normalize_primary_expression_grouping_spine
        {| phase1_primary_expression_spine_branch := index;
           phase1_primary_expression_spine_selected := selected |} =
        Some refined.
Proof.
  intros index item path input rest selected Hnth Hderive.
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_tuple_expression_spine_total_from_derivation
        path input rest selected Hderive)
      as [tuple_expression [Htuple _]].
    exists (Phase1PrimaryExpressionTupleRefined tuple_expression).
    cbn.
    rewrite Htuple.
    reflexivity.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_parenthesized_expression_spine_total_from_derivation
          path input rest selected Hderive)
        as [parenthesized [Hparenthesized _]].
      exists (Phase1PrimaryExpressionParenthesizedRefined parenthesized).
      cbn.
      rewrite Hparenthesized.
      reflexivity.
    + exists
        (Phase1PrimaryExpressionOtherRetained (S (S index)) selected).
      reflexivity.
Qed.

Theorem
  phase1_surface_normalize_primary_expression_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "primary_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_primary_expression_grouping_tree tree =
        Some refined /\
      phase1_surface_primary_expression_grouping_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "primary_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_primary_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "primary_expression"))
      phase1_surface_primary_expression_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  pose proof
    (phase1_surface_primary_expression_branch_valid_total_from_derivation
      index item _ _ _ selected Hnth Hselected) as Hvalid.
  let expression := constr:(
    {| phase1_primary_expression_spine_branch := index;
       phase1_primary_expression_spine_selected := selected |}) in
  assert (Hspine :
    phase1_surface_normalize_primary_expression_spine tree =
      Some expression).
  {
    rewrite Htree, Hsubtree.
    unfold phase1_surface_normalize_primary_expression_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn.
    rewrite Hvalid.
    reflexivity.
  }
  destruct
    (phase1_surface_normalize_primary_expression_grouping_spine_total_from_branch_derivation
      index item _ _ _ selected Hnth Hselected)
    as [refined Hgrouping].
  exists refined.
  split.
  - unfold phase1_surface_normalize_primary_expression_grouping_tree.
    rewrite Hspine.
    exact Hgrouping.
  - eapply
      phase1_surface_normalize_primary_expression_grouping_tree_round_trip.
    unfold phase1_surface_normalize_primary_expression_grouping_tree.
    rewrite Hspine.
    exact Hgrouping.
Qed.
