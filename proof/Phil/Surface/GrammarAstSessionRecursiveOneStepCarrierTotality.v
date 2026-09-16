From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSessionRecursiveOneStepCarrierSpine
  GrammarAstSessionRecursivePayloadTotality
  GrammarAstSessionTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the shallow current-node recursive payload lift from #1109. *)

Lemma phase1_surface_selected_recursive_derivation :
  forall path input rest selected_tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression")
      input rest
      (PTNonterminal "session_expression"
        (PTAlternative 0
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative 5 selected_tree)))) ->
    exists recursive_path,
      Derives phase1_surface_rules recursive_path
        phase1_surface_recursive_session_expression_for_totality
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
            (PTAlternative 5 selected_tree))))
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
          (PTAlternative 5 selected_tree)))
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
        (PTAlternative 5 selected_tree))
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
      input rest (PTAlternative 5 selected_tree)
      Hnonreference_body)
    as [recursive_index [recursive_item [selected_recursive
      [Hrecursive_nth [Hrecursive_tree Hrecursive]]]]].
  cbn in Hrecursive_tree.
  inversion Hrecursive_tree; subst recursive_index selected_recursive.
  cbn in Hrecursive_nth.
  inversion Hrecursive_nth; subst recursive_item.
  eexists.
  exact Hrecursive.
Qed.

Theorem
  phase1_surface_normalize_recursive_one_step_session_spine_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_continue_mutual_recursive_session_spine_tree session) ->
    exists refined,
      phase1_surface_normalize_recursive_one_step_session_spine session =
        Some refined.
Proof.
  intros path input rest session Hderive.
  destruct session as [nonreference | reference_tree].
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |choice
      |choice
      |terminal
      |selected_tree
      |payload].
    + exists
        (Phase1RecursiveOneStepNonreferenceSession
          (Phase1RecursiveOneStepTransferSession
            direction parameter boundary guard continuation)).
      reflexivity.
    + exists
        (Phase1RecursiveOneStepNonreferenceSession
          (Phase1RecursiveOneStepSelectSession choice)).
      reflexivity.
    + exists
        (Phase1RecursiveOneStepNonreferenceSession
          (Phase1RecursiveOneStepOfferSession choice)).
      reflexivity.
    + exists
        (Phase1RecursiveOneStepNonreferenceSession
          (Phase1RecursiveOneStepEndSession terminal)).
      reflexivity.
    + cbn in Hderive.
      destruct
        (phase1_surface_selected_recursive_derivation
          path input rest selected_tree Hderive)
        as [recursive_path Hrecursive].
      destruct
        (phase1_surface_normalize_recursive_session_payload_spine_total_from_derivation
          recursive_path input rest selected_tree Hrecursive)
        as [recursive_payload [Hpayload Hpayload_tree]].
      exists
        (Phase1RecursiveOneStepNonreferenceSession
          (Phase1RecursiveOneStepRecursiveSession recursive_payload)).
      cbn.
      rewrite Hpayload.
      reflexivity.
    + exists
        (Phase1RecursiveOneStepNonreferenceSession
          (Phase1RecursiveOneStepContinueSession payload)).
      reflexivity.
  - exists (Phase1RecursiveOneStepStaticReferenceSession reference_tree).
    reflexivity.
Qed.
