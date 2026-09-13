From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferCarrierSpine
  GrammarAstSessionTransferPayloadTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the transfer-refined session_expression carrier. *)

Theorem
  phase1_surface_normalize_transfer_refined_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "session_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_transfer_refined_session_tree tree =
        Some refined /\
      phase1_surface_transfer_refined_session_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_session_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "session_expression"))
      phase1_surface_session_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_nonreference_session_spine_total_from_derivation
        (descend
          (descend path (AtNonterminal "session_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [base [Hbase Hbase_round_trip]].
    destruct
      (phase1_surface_normalize_transfer_refined_nonreference_session_tree_total_from_derivation
        (descend
          (descend path (AtNonterminal "session_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [refined [Hrefined Hrefined_round_trip]].
    assert (Hlift :
      phase1_surface_normalize_transfer_refined_nonreference_session_spine base =
        Some refined).
    {
      unfold
        phase1_surface_normalize_transfer_refined_nonreference_session_tree
        in Hrefined.
      rewrite Hbase in Hrefined.
      exact Hrefined.
    }
    let session := constr:(Phase1NonreferenceSessionSpine base) in
    let result := constr:(Phase1TransferRefinedNonreferenceSession refined) in
    assert (Hsession :
      phase1_surface_normalize_session_spine tree = Some session).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_session_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hbase.
      reflexivity.
    }
    assert (Hresult :
      phase1_surface_normalize_transfer_refined_session_tree tree =
        Some result).
    {
      unfold phase1_surface_normalize_transfer_refined_session_tree.
      rewrite Hsession.
      cbn.
      rewrite Hlift.
      reflexivity.
    }
    exists result.
    split.
    + exact Hresult.
    + eapply
        phase1_surface_normalize_transfer_refined_session_tree_round_trip.
      exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      let session := constr:(Phase1StaticReferenceSessionSpine selected) in
      let result := constr:(Phase1TransferRefinedStaticReferenceSession selected) in
      assert (Hsession :
        phase1_surface_normalize_session_spine tree = Some session).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_session_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        reflexivity.
      }
      assert (Hresult :
        phase1_surface_normalize_transfer_refined_session_tree tree =
          Some result).
      {
        unfold phase1_surface_normalize_transfer_refined_session_tree.
        rewrite Hsession.
        reflexivity.
      }
      exists result.
      split.
      * exact Hresult.
      * eapply
          phase1_surface_normalize_transfer_refined_session_tree_round_trip.
        exact Hresult.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
