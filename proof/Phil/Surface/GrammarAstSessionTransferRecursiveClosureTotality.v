From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String Lia.

From Phil.Surface Require Import
  GrammarAstSessionTransferRecursiveClosureSpine
  GrammarAstSessionTransferContinuationCarrierTotality
  GrammarDerivationLookahead.

Import ListNotations.
Open Scope string_scope.

(*
  Derivation-driven totality for the recursive send/receive continuation
  carrier.  A certified transfer consumes its leading send/receive keyword
  before entering the continuation, so the continuation begins on a strictly
  shorter token suffix.  Hence S (length input) is sufficient recursive fuel.
*)

Lemma phase1_surface_derivation_rest_length_le_input :
  forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    List.length rest <= List.length input.
Proof.
  intros path expression input rest tree Hderive.
  destruct
    (derives_consumes_prefix
      phase1_surface_rules path expression input rest tree Hderive)
    as [consumed Hprefix].
  rewrite Hprefix, List.length_app.
  lia.
Qed.

Lemma phase1_surface_transfer_continuation_derivation_shorter :
  forall direction path input rest tree transfer,
    Derives phase1_surface_rules path
      (phase1_surface_session_transfer_expression_for_totality direction)
      input rest tree ->
    phase1_surface_guard_refined_boundary_typed_session_transfer_spine_tree
      transfer = tree ->
    phase1_guard_refined_transfer_direction transfer = direction ->
    exists continuation_path continuation_input continuation_rest,
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_guard_refined_transfer_continuation_tree transfer) /\
      List.length continuation_input < List.length input.
Proof.
  intros direction path input rest tree
    [actual_direction parameter boundary guard continuation]
    Hderive Htree Hdirection.
  cbn in Hdirection.
  subst actual_direction.
  unfold phase1_surface_session_transfer_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral (phase1_surface_session_transfer_keyword direction);
        ELiteral "(";
        ENonterminal "term_param";
        ELiteral ")";
        phase1_surface_named_annotation_expression_for_totality
          "using" "static_reference";
        phase1_surface_named_annotation_expression_for_totality
          "when" "proposition";
        ELiteral "then";
        ENonterminal "session_expression"
      ]
      input rest tree Hderive)
    as [trees [Hsequence Hitems]].
  cbn in Htree.
  rewrite Hsequence in Htree.
  inversion Htree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral (phase1_surface_session_transfer_keyword direction))
      _ _ _ |- _ =>
      inversion Hkeyword; subst; clear Hkeyword
  end.
  match goal with
  | Hopen : Derives phase1_surface_rules _ (ELiteral "(") _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hopen) as Hopen_length
  end.
  match goal with
  | Hparameter : Derives phase1_surface_rules _
      (ENonterminal "term_param") _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hparameter) as Hparameter_length
  end.
  match goal with
  | Hclose : Derives phase1_surface_rules _ (ELiteral ")") _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hclose) as Hclose_length
  end.
  match goal with
  | Hboundary : Derives phase1_surface_rules _
      (phase1_surface_named_annotation_expression_for_totality
        "using" "static_reference") _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hboundary) as Hboundary_length
  end.
  match goal with
  | Hguard : Derives phase1_surface_rules _
      (phase1_surface_named_annotation_expression_for_totality
        "when" "proposition") _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hguard) as Hguard_length
  end.
  match goal with
  | Hthen : Derives phase1_surface_rules _ (ELiteral "then") _ _ _ |- _ =>
      pose proof
        (phase1_surface_derivation_rest_length_le_input
          _ _ _ _ _ Hthen) as Hthen_length
  end.
  match goal with
  | Hcontinuation : Derives phase1_surface_rules ?continuation_path
      (ENonterminal "session_expression")
      ?continuation_input ?continuation_rest continuation |- _ =>
      exists continuation_path, continuation_input, continuation_rest;
      split;
      [ exact Hcontinuation
      | cbn in *; lia ]
  end.
Qed.

Lemma phase1_surface_guard_refined_transfer_continuation_derivation_shorter :
  forall path input rest tree transfer,
    Derives phase1_surface_rules path (ENonterminal "session_expression")
      input rest tree ->
    phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
      (Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession
        (Phase1GuardRefinedBoundaryTypedTransferSession transfer)) = tree ->
    exists continuation_path continuation_input continuation_rest,
      Derives phase1_surface_rules continuation_path
        (ENonterminal "session_expression")
        continuation_input continuation_rest
        (phase1_guard_refined_transfer_continuation_tree transfer) /\
      List.length continuation_input < List.length input.
Proof.
  intros path input rest tree
    [direction parameter boundary guard continuation]
    Hderive Htree.
  rewrite <- Htree in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_expression"
      input rest
      (phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
        (Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession
          (Phase1GuardRefinedBoundaryTypedTransferSession
            {| phase1_guard_refined_transfer_direction := direction;
               phase1_guard_refined_transfer_parameter := parameter;
               phase1_guard_refined_transfer_boundary := boundary;
               phase1_guard_refined_transfer_guard := guard;
               phase1_guard_refined_transfer_continuation_tree := continuation |})))
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
        (phase1_surface_guard_refined_boundary_typed_transfer_nonreference_session_spine_tree
          (Phase1GuardRefinedBoundaryTypedTransferSession
            {| phase1_guard_refined_transfer_direction := direction;
               phase1_guard_refined_transfer_parameter := parameter;
               phase1_guard_refined_transfer_boundary := boundary;
               phase1_guard_refined_transfer_guard := guard;
               phase1_guard_refined_transfer_continuation_tree := continuation |})))
      Hbody)
    as [index [item [selected [Hnth [Hselected_tree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    cbn in Hselected_tree.
    inversion Hselected_tree; subst selected.
    destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules
        (descend
          (descend path (AtNonterminal "session_expression"))
          (AtAlternative 0))
        "nonreference_session_expression"
        input rest
        (phase1_surface_guard_refined_boundary_typed_transfer_nonreference_session_spine_tree
          (Phase1GuardRefinedBoundaryTypedTransferSession
            {| phase1_guard_refined_transfer_direction := direction;
               phase1_guard_refined_transfer_parameter := parameter;
               phase1_guard_refined_transfer_boundary := boundary;
               phase1_guard_refined_transfer_guard := guard;
               phase1_guard_refined_transfer_continuation_tree := continuation |}))
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
        phase1_surface_rules
        (descend
          (descend
            (descend path (AtNonterminal "session_expression"))
            (AtAlternative 0))
          (AtNonterminal "nonreference_session_expression"))
        phase1_surface_nonreference_session_items_for_totality
        input rest
        (PTAlternative
          (phase1_surface_session_transfer_index direction)
          (phase1_surface_guard_refined_boundary_typed_session_transfer_spine_tree
            {| phase1_guard_refined_transfer_direction := direction;
               phase1_guard_refined_transfer_parameter := parameter;
               phase1_guard_refined_transfer_boundary := boundary;
               phase1_guard_refined_transfer_guard := guard;
               phase1_guard_refined_transfer_continuation_tree := continuation |}))
        Hnonreference_body)
      as [transfer_index
          [transfer_item
            [transfer_tree
              [Htransfer_nth [Htransfer_tree Htransfer]]]]].
    destruct direction.
    + cbn in Htransfer_tree.
      inversion Htransfer_tree; subst transfer_index transfer_tree.
      cbn in Htransfer_nth.
      inversion Htransfer_nth; subst transfer_item.
      eapply
        (phase1_surface_transfer_continuation_derivation_shorter
          Phase1SessionSend
          _ _ _ _
          {| phase1_guard_refined_transfer_direction := Phase1SessionSend;
             phase1_guard_refined_transfer_parameter := parameter;
             phase1_guard_refined_transfer_boundary := boundary;
             phase1_guard_refined_transfer_guard := guard;
             phase1_guard_refined_transfer_continuation_tree := continuation |}).
      * exact Htransfer.
      * reflexivity.
      * reflexivity.
    + cbn in Htransfer_tree.
      inversion Htransfer_tree; subst transfer_index transfer_tree.
      cbn in Htransfer_nth.
      inversion Htransfer_nth; subst transfer_item.
      eapply
        (phase1_surface_transfer_continuation_derivation_shorter
          Phase1SessionReceive
          _ _ _ _
          {| phase1_guard_refined_transfer_direction := Phase1SessionReceive;
             phase1_guard_refined_transfer_parameter := parameter;
             phase1_guard_refined_transfer_boundary := boundary;
             phase1_guard_refined_transfer_guard := guard;
             phase1_guard_refined_transfer_continuation_tree := continuation |}).
      * exact Htransfer.
      * reflexivity.
      * reflexivity.
  - cbn in Hselected_tree.
    discriminate Hselected_tree.
Qed.

Lemma phase1_surface_normalize_recursive_transfer_session_spine_fuel_total_bounded :
  forall fuel path input rest tree session,
    List.length input < fuel ->
    Derives phase1_surface_rules path (ENonterminal "session_expression")
      input rest tree ->
    phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
      session = tree ->
    exists refined,
      phase1_surface_normalize_recursive_transfer_session_spine_fuel
        fuel session = Some refined.
Proof.
  induction fuel as [|fuel IH];
    intros path input rest tree session Hfuel Hderive Htree.
  - lia.
  - destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [transfer | selected | selected | selected | selected | selected].
      * destruct transfer as [direction parameter boundary guard continuation].
        destruct
          (phase1_surface_guard_refined_transfer_continuation_derivation_shorter
            path input rest tree
            {| phase1_guard_refined_transfer_direction := direction;
               phase1_guard_refined_transfer_parameter := parameter;
               phase1_guard_refined_transfer_boundary := boundary;
               phase1_guard_refined_transfer_guard := guard;
               phase1_guard_refined_transfer_continuation_tree := continuation |}
            Hderive Htree)
          as [continuation_path
              [continuation_input
                [continuation_rest
                  [Hcontinuation Hcontinuation_shorter]]]].
        destruct
          (phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree_total_from_derivation
            continuation_path continuation_input continuation_rest
            continuation Hcontinuation)
          as [continuation_session
              [Hcontinuation_normalize Hcontinuation_tree]].
        assert (Hcontinuation_fuel :
          List.length continuation_input < fuel) by lia.
        destruct
          (IH continuation_path continuation_input continuation_rest
            continuation continuation_session
            Hcontinuation_fuel Hcontinuation Hcontinuation_tree)
          as [recursive_continuation Hrecursive_continuation].
        exists
          (Phase1RecursiveTransferNonreferenceSession
            (Phase1RecursiveTransferPayloadSession
              direction parameter boundary guard recursive_continuation)).
        cbn
          [ phase1_surface_normalize_continuation_refined_transfer_session_spine;
            phase1_surface_normalize_continuation_refined_transfer_nonreference_session_spine;
            phase1_surface_normalize_continuation_refined_session_transfer_spine ].
        rewrite Hcontinuation_normalize.
        cbn.
        rewrite Hrecursive_continuation.
        reflexivity.
      * exists
          (Phase1RecursiveTransferNonreferenceSession
            (Phase1RecursiveTransferOpaqueSelectSession selected)).
        reflexivity.
      * exists
          (Phase1RecursiveTransferNonreferenceSession
            (Phase1RecursiveTransferOpaqueOfferSession selected)).
        reflexivity.
      * exists
          (Phase1RecursiveTransferNonreferenceSession
            (Phase1RecursiveTransferOpaqueEndSession selected)).
        reflexivity.
      * exists
          (Phase1RecursiveTransferNonreferenceSession
            (Phase1RecursiveTransferOpaqueRecursiveSession selected)).
        reflexivity.
      * exists
          (Phase1RecursiveTransferNonreferenceSession
            (Phase1RecursiveTransferOpaqueContinueSession selected)).
        reflexivity.
    + exists (Phase1RecursiveTransferStaticReferenceSession reference_tree).
      reflexivity.
Qed.

Theorem phase1_surface_normalize_recursive_transfer_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "session_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_recursive_transfer_session_tree_fuel
        (S (List.length input)) tree = Some refined /\
      phase1_surface_recursive_transfer_session_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_guard_refined_boundary_typed_transfer_session_tree_total_from_derivation
      path input rest tree Hderive)
    as [session [Hsession Hsession_tree]].
  destruct
    (phase1_surface_normalize_recursive_transfer_session_spine_fuel_total_bounded
      (S (List.length input)) path input rest tree session
      (Nat.lt_succ_diag_r (List.length input))
      Hderive Hsession_tree)
    as [refined Hrefined].
  assert (Hresult :
    phase1_surface_normalize_recursive_transfer_session_tree_fuel
      (S (List.length input)) tree = Some refined).
  {
    unfold phase1_surface_normalize_recursive_transfer_session_tree_fuel.
    rewrite Hsession.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_recursive_transfer_session_tree_fuel_round_trip.
    exact Hresult.
Qed.
