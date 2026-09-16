From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionContinueOneStepCarrierSpine
  GrammarAstSessionContinuePayloadTotality
  GrammarAstSessionEndRecursiveCarrierTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the shallow current-node `continue identifier` lift from #1086. *)

Lemma phase1_surface_selected_continue_derivation :
  forall path input rest selected_tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression")
      input rest
      (PTNonterminal "session_expression"
        (PTAlternative 0
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative 6 selected_tree)))) ->
    exists continue_path,
      Derives phase1_surface_rules continue_path
        phase1_surface_continue_session_expression_for_totality
        input rest selected_tree.
Proof.
  intros path input rest selected_tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_expression"
      input rest
      (PTNonterminal "session_expression"
        (PTAlternative 0
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative 6 selected_tree))))
      Hderive)
    as [body [subtree [Hlookup [Hnode Hbody]]]].
  rewrite phase1_surface_session_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn in Hnode.
  inversion Hnode; subst subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "session_expression"))
      phase1_surface_session_items_for_totality
      input rest
      (PTAlternative 0
        (PTNonterminal "nonreference_session_expression"
          (PTAlternative 6 selected_tree)))
      Hbody)
    as [index [item [selected [Hnth [Hselected_tree Hselected]]]]].
  cbn in Hselected_tree.
  inversion Hselected_tree; subst index selected.
  cbn in Hnth.
  inversion Hnth; subst item.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules _
      "nonreference_session_expression"
      input rest
      (PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree))
      Hselected)
    as [nonreference_body
      [nonreference_subtree
        [Hnonreference_lookup [Hnonreference_node Hnonreference_body]]]].
  rewrite phase1_surface_nonreference_session_lookup_for_totality
    in Hnonreference_lookup.
  inversion Hnonreference_lookup; subst nonreference_body.
  cbn in Hnonreference_node.
  inversion Hnonreference_node; subst nonreference_subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules _
      phase1_surface_nonreference_session_items_for_totality
      input rest (PTAlternative 6 selected_tree)
      Hnonreference_body)
    as [continue_index [continue_item [selected_continue
      [Hcontinue_nth [Hcontinue_tree Hcontinue]]]]].
  cbn in Hcontinue_tree.
  inversion Hcontinue_tree; subst continue_index selected_continue.
  cbn in Hcontinue_nth.
  inversion Hcontinue_nth; subst continue_item.
  eexists.
  exact Hcontinue.
Qed.

Theorem
  phase1_surface_normalize_continue_refined_end_recursive_session_spine_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_end_refined_recursive_session_spine_tree session) ->
    exists refined,
      phase1_surface_normalize_continue_refined_end_recursive_session_spine
        session = Some refined.
Proof.
  intros path input rest session Hderive.
  destruct session as [nonreference | reference_tree].
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |choice
      |choice
      |terminal
      |selected_tree
      |selected_tree].
    + exists
        (Phase1ContinueRefinedEndRecursiveNonreferenceSession
          (Phase1ContinueRefinedEndRecursiveTransferSession
            direction parameter boundary guard continuation)).
      reflexivity.
    + exists
        (Phase1ContinueRefinedEndRecursiveNonreferenceSession
          (Phase1ContinueRefinedEndRecursiveSelectSession choice)).
      reflexivity.
    + exists
        (Phase1ContinueRefinedEndRecursiveNonreferenceSession
          (Phase1ContinueRefinedEndRecursiveOfferSession choice)).
      reflexivity.
    + exists
        (Phase1ContinueRefinedEndRecursiveNonreferenceSession
          (Phase1ContinueRefinedEndRecursiveEndSession terminal)).
      reflexivity.
    + exists
        (Phase1ContinueRefinedEndRecursiveNonreferenceSession
          (Phase1ContinueRefinedEndRecursiveRecursiveSession selected_tree)).
      reflexivity.
    + cbn in Hderive.
      destruct
        (phase1_surface_selected_continue_derivation
          path input rest selected_tree Hderive)
        as [continue_path Hcontinue].
      destruct
        (phase1_surface_normalize_continue_session_payload_spine_total_from_derivation
          continue_path input rest selected_tree Hcontinue)
        as [payload [Hpayload Hpayload_tree]].
      exists
        (Phase1ContinueRefinedEndRecursiveNonreferenceSession
          (Phase1ContinueRefinedEndRecursiveContinueSession payload)).
      cbn.
      rewrite Hpayload.
      reflexivity.
  - exists
      (Phase1ContinueRefinedEndRecursiveStaticReferenceSession reference_tree).
    reflexivity.
Qed.
