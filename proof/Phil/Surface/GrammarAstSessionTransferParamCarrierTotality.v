From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferParamCarrierSpine
  GrammarAstSessionTransferPayloadTotality
  GrammarAstSessionTransferCarrierTotality
  GrammarAstTermParamTypeTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the term-parameter-refined transfer/session carrier lift. *)

Lemma phase1_surface_normalize_typed_session_transfer_layers_total_from_derivation :
  forall direction path input rest tree,
    Derives phase1_surface_rules path
      (phase1_surface_session_transfer_expression_for_totality direction)
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_session_transfer_spine direction tree = Some base /\
      phase1_surface_normalize_typed_session_transfer_spine base = Some refined /\
      phase1_surface_typed_session_transfer_spine_tree refined = tree.
Proof.
  intros direction path input rest tree Hderive.
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
    as [trees [Htree Hitems]].
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
      _ _ ?keyword_tree,
    Hopen : Derives phase1_surface_rules _
      (ELiteral "(") _ _ ?open_tree,
    Hparameter : Derives phase1_surface_rules _
      (ENonterminal "term_param") _ _ ?parameter_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral ")") _ _ ?close_tree,
    Hboundary : Derives phase1_surface_rules _
      (phase1_surface_named_annotation_expression_for_totality
        "using" "static_reference") _ _ ?boundary_tree,
    Hguard : Derives phase1_surface_rules _
      (phase1_surface_named_annotation_expression_for_totality
        "when" "proposition") _ _ ?guard_tree,
    Hthen : Derives phase1_surface_rules _
      (ELiteral "then") _ _ ?then_tree,
    Hcontinuation : Derives phase1_surface_rules _
      (ENonterminal "session_expression") _ _ ?continuation_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _
          (phase1_surface_session_transfer_keyword direction)
          _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "(" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "term_param" _ _ _ parameter_tree Hparameter)
        as Hparameter_validate;
      destruct
        (phase1_surface_normalize_term_param_type_spine_total_from_derivation
          _ _ _ parameter_tree Hparameter)
        as [parameter [Hparameter_normalize Hparameter_round_trip]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ")" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_normalize_optional_named_annotation_total_from_derivation
          "using" "static_reference" _ _ _ boundary_tree Hboundary)
        as [boundary [Hboundary_normalize Hboundary_round_trip]];
      destruct
        (phase1_surface_normalize_optional_named_annotation_total_from_derivation
          "when" "proposition" _ _ _ guard_tree Hguard)
        as [guard [Hguard_normalize Hguard_round_trip]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "then" _ _ then_tree Hthen)
        as [then_tail [_ [_ Hthen_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "session_expression" _ _ _ continuation_tree Hcontinuation)
        as Hcontinuation_validate;
      let base := constr:(
        {| phase1_session_transfer_direction := direction;
           phase1_session_transfer_parameter_tree := parameter_tree;
           phase1_session_transfer_boundary_tree := boundary;
           phase1_session_transfer_guard_tree := guard;
           phase1_session_transfer_continuation_tree := continuation_tree |}) in
      let refined := constr:(
        {| phase1_typed_session_transfer_direction := direction;
           phase1_typed_session_transfer_parameter := parameter;
           phase1_typed_session_transfer_boundary_tree := boundary;
           phase1_typed_session_transfer_guard_tree := guard;
           phase1_typed_session_transfer_continuation_tree := continuation_tree |}) in
      assert (Hbase :
        phase1_surface_normalize_session_transfer_spine direction tree = Some base);
      [ rewrite Htree, Hkeyword_tree, Hopen_tree, Hclose_tree, Hthen_tree;
        unfold phase1_surface_normalize_session_transfer_spine,
          phase1_surface_expect_sequence,
          phase1_surface_exact8,
          phase1_surface_expect_literal;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hparameter_validate;
        rewrite Hboundary_normalize;
        rewrite Hguard_normalize;
        rewrite Hcontinuation_validate;
        reflexivity
      | assert (Hrefined :
          phase1_surface_normalize_typed_session_transfer_spine base =
            Some refined);
        [ cbn;
          rewrite Hparameter_normalize;
          reflexivity
        | exists base, refined;
          split;
          [ exact Hbase
          | split;
            [ exact Hrefined
            | transitivity (phase1_surface_session_transfer_spine_tree base);
              [ eapply
                  phase1_surface_normalize_typed_session_transfer_spine_round_trip;
                exact Hrefined
              | eapply phase1_surface_normalize_session_transfer_spine_round_trip;
                exact Hbase ] ] ] ] ]
  end.
Qed.

Theorem
  phase1_surface_normalize_typed_transfer_nonreference_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_session_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
        Some refined /\
      phase1_surface_typed_transfer_nonreference_session_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "nonreference_session_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_nonreference_session_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "nonreference_session_expression"))
      phase1_surface_nonreference_session_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_typed_session_transfer_layers_total_from_derivation
        Phase1SessionSend
        (descend
          (descend path (AtNonterminal "nonreference_session_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [transfer [typed [Htransfer [Htyped Htyped_tree]]]].
    let base := constr:(
      {| phase1_nonreference_session_spine_tag := Phase1SendSession;
         phase1_nonreference_session_spine_selected_tree := selected |}) in
    let middle := constr:(Phase1RefinedTransferSession transfer) in
    let result := constr:(Phase1TypedTransferSession typed) in
    assert (Hbase :
      phase1_surface_normalize_nonreference_session_spine tree = Some base).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_nonreference_session_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      reflexivity.
    }
    assert (Hmiddle :
      phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
        Some middle).
    {
      unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
      rewrite Hbase.
      cbn.
      rewrite Htransfer.
      reflexivity.
    }
    assert (Hresult :
      phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
        Some result).
    {
      unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree.
      rewrite Hmiddle.
      cbn.
      rewrite Htyped.
      reflexivity.
    }
    exists result.
    split.
    + exact Hresult.
    + eapply
        phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip.
      exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_typed_session_transfer_layers_total_from_derivation
          Phase1SessionReceive
          (descend
            (descend path (AtNonterminal "nonreference_session_expression"))
            (AtAlternative 1))
          input rest selected Hselected)
        as [transfer [typed [Htransfer [Htyped Htyped_tree]]]].
      let base := constr:(
        {| phase1_nonreference_session_spine_tag := Phase1ReceiveSession;
           phase1_nonreference_session_spine_selected_tree := selected |}) in
      let middle := constr:(Phase1RefinedTransferSession transfer) in
      let result := constr:(Phase1TypedTransferSession typed) in
      assert (Hbase :
        phase1_surface_normalize_nonreference_session_spine tree = Some base).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_nonreference_session_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        reflexivity.
      }
      assert (Hmiddle :
        phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
          Some middle).
      {
        unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
        rewrite Hbase.
        cbn.
        rewrite Htransfer.
        reflexivity.
      }
      assert (Hresult :
        phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
          Some result).
      {
        unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree.
        rewrite Hmiddle.
        cbn.
        rewrite Htyped.
        reflexivity.
      }
      exists result.
      split.
      * exact Hresult.
      * eapply
          phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip.
        exact Hresult.
    + destruct index as [|index].
      * cbn in Hnth.
        inversion Hnth; subst item.
        let base := constr:(
          {| phase1_nonreference_session_spine_tag := Phase1SelectSession;
             phase1_nonreference_session_spine_selected_tree := selected |}) in
        let middle := constr:(Phase1OpaqueSelectSession selected) in
        let result := constr:(Phase1TypedOpaqueSelectSession selected) in
        assert (Hbase :
          phase1_surface_normalize_nonreference_session_spine tree = Some base).
        {
          rewrite Htree, Hsubtree.
          unfold phase1_surface_normalize_nonreference_session_spine,
            phase1_surface_expect_nonterminal,
            phase1_surface_expect_alternative.
          cbn.
          reflexivity.
        }
        assert (Hmiddle :
          phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
            Some middle).
        {
          unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
          rewrite Hbase.
          reflexivity.
        }
        assert (Hresult :
          phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
            Some result).
        {
          unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree.
          rewrite Hmiddle.
          reflexivity.
        }
        exists result.
        split.
        -- exact Hresult.
        -- eapply
             phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip.
           exact Hresult.
      * destruct index as [|index].
        -- cbn in Hnth.
           inversion Hnth; subst item.
           let base := constr:(
             {| phase1_nonreference_session_spine_tag := Phase1OfferSession;
                phase1_nonreference_session_spine_selected_tree := selected |}) in
           let middle := constr:(Phase1OpaqueOfferSession selected) in
           let result := constr:(Phase1TypedOpaqueOfferSession selected) in
           assert (Hbase :
             phase1_surface_normalize_nonreference_session_spine tree = Some base).
           {
             rewrite Htree, Hsubtree.
             unfold phase1_surface_normalize_nonreference_session_spine,
               phase1_surface_expect_nonterminal,
               phase1_surface_expect_alternative.
             cbn.
             reflexivity.
           }
           assert (Hmiddle :
             phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
               Some middle).
           {
             unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
             rewrite Hbase.
             reflexivity.
           }
           assert (Hresult :
             phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
               Some result).
           {
             unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree.
             rewrite Hmiddle.
             reflexivity.
           }
           exists result.
           split.
           ++ exact Hresult.
           ++ eapply
                phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip.
              exact Hresult.
        -- destruct index as [|index].
           ++ cbn in Hnth.
              inversion Hnth; subst item.
              let base := constr:(
                {| phase1_nonreference_session_spine_tag := Phase1EndSession;
                   phase1_nonreference_session_spine_selected_tree := selected |}) in
              let middle := constr:(Phase1OpaqueEndSession selected) in
              let result := constr:(Phase1TypedOpaqueEndSession selected) in
              assert (Hbase :
                phase1_surface_normalize_nonreference_session_spine tree = Some base).
              {
                rewrite Htree, Hsubtree.
                unfold phase1_surface_normalize_nonreference_session_spine,
                  phase1_surface_expect_nonterminal,
                  phase1_surface_expect_alternative.
                cbn.
                reflexivity.
              }
              assert (Hmiddle :
                phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
                  Some middle).
              {
                unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
                rewrite Hbase.
                reflexivity.
              }
              assert (Hresult :
                phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
                  Some result).
              {
                unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree.
                rewrite Hmiddle.
                reflexivity.
              }
              exists result.
              split.
              ** exact Hresult.
              ** eapply
                   phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip.
                 exact Hresult.
           ++ destruct index as [|index].
              ** cbn in Hnth.
                 inversion Hnth; subst item.
                 let base := constr:(
                   {| phase1_nonreference_session_spine_tag := Phase1RecursiveSession;
                      phase1_nonreference_session_spine_selected_tree := selected |}) in
                 let middle := constr:(Phase1OpaqueRecursiveSession selected) in
                 let result := constr:(Phase1TypedOpaqueRecursiveSession selected) in
                 assert (Hbase :
                   phase1_surface_normalize_nonreference_session_spine tree = Some base).
                 {
                   rewrite Htree, Hsubtree.
                   unfold phase1_surface_normalize_nonreference_session_spine,
                     phase1_surface_expect_nonterminal,
                     phase1_surface_expect_alternative.
                   cbn.
                   reflexivity.
                 }
                 assert (Hmiddle :
                   phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
                     Some middle).
                 {
                   unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
                   rewrite Hbase.
                   reflexivity.
                 }
                 assert (Hresult :
                   phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
                     Some result).
                 {
                   unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree.
                   rewrite Hmiddle.
                   reflexivity.
                 }
                 exists result.
                 split.
                 --- exact Hresult.
                 --- eapply
                      phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip.
                     exact Hresult.
              ** destruct index as [|index].
                 --- cbn in Hnth.
                     inversion Hnth; subst item.
                     let base := constr:(
                       {| phase1_nonreference_session_spine_tag := Phase1ContinueSession;
                          phase1_nonreference_session_spine_selected_tree := selected |}) in
                     let middle := constr:(Phase1OpaqueContinueSession selected) in
                     let result := constr:(Phase1TypedOpaqueContinueSession selected) in
                     assert (Hbase :
                       phase1_surface_normalize_nonreference_session_spine tree = Some base).
                     {
                       rewrite Htree, Hsubtree.
                       unfold phase1_surface_normalize_nonreference_session_spine,
                         phase1_surface_expect_nonterminal,
                         phase1_surface_expect_alternative.
                       cbn.
                       reflexivity.
                     }
                     assert (Hmiddle :
                       phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
                         Some middle).
                     {
                       unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
                       rewrite Hbase.
                       reflexivity.
                     }
                     assert (Hresult :
                       phase1_surface_normalize_typed_transfer_nonreference_session_tree tree =
                         Some result).
                     {
                       unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree.
                       rewrite Hmiddle.
                       reflexivity.
                     }
                     exists result.
                     split.
                     +++ exact Hresult.
                     +++ eapply
                          phase1_surface_normalize_typed_transfer_nonreference_session_tree_round_trip.
                         exact Hresult.
                 --- cbn in Hnth.
                     discriminate Hnth.
Qed.

Theorem phase1_surface_normalize_typed_transfer_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "session_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_typed_transfer_session_tree tree = Some refined /\
      phase1_surface_typed_transfer_session_spine_tree refined = tree.
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
      (phase1_surface_normalize_transfer_refined_session_tree_total_from_derivation
        path input rest tree Hderive)
      as [middle [Hmiddle Hmiddle_tree]].
    destruct
      (phase1_surface_normalize_typed_transfer_nonreference_session_tree_total_from_derivation
        (descend
          (descend path (AtNonterminal "session_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [typed_nonreference [Htyped_nonreference Htyped_nonreference_tree]].
    destruct
      (phase1_surface_normalize_nonreference_session_spine_total_from_derivation
        (descend
          (descend path (AtNonterminal "session_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [base_nonreference [Hbase_nonreference Hbase_nonreference_tree]].
    let base_session := constr:(Phase1NonreferenceSessionSpine base_nonreference) in
    let transfer_nonreference := constr:(
      match middle with
      | Phase1TransferRefinedNonreferenceSession n => n
      | Phase1TransferRefinedStaticReferenceSession _ =>
          Phase1OpaqueEndSession selected
      end) in
    assert (Hsession :
      phase1_surface_normalize_session_spine tree = Some base_session).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_session_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hbase_nonreference.
      reflexivity.
    }
    unfold phase1_surface_normalize_transfer_refined_session_tree in Hmiddle.
    rewrite Hsession in Hmiddle.
    cbn in Hmiddle.
    destruct
      (phase1_surface_normalize_transfer_refined_nonreference_session_spine
        base_nonreference)
      as [middle_nonreference |] eqn:Hlift; try discriminate Hmiddle.
    inversion Hmiddle; subst middle.
    unfold phase1_surface_normalize_typed_transfer_nonreference_session_tree
      in Htyped_nonreference.
    destruct
      (phase1_surface_normalize_transfer_refined_nonreference_session_tree selected)
      as [selected_middle |] eqn:Hselected_middle;
      try discriminate Htyped_nonreference.
    assert (Hselected_middle_eq : selected_middle = middle_nonreference).
    {
      unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree
        in Hselected_middle.
      rewrite Hbase_nonreference in Hselected_middle.
      rewrite Hlift in Hselected_middle.
      inversion Hselected_middle.
      reflexivity.
    }
    subst selected_middle.
    let result := constr:(Phase1TypedTransferNonreferenceSession typed_nonreference) in
    assert (Hresult :
      phase1_surface_normalize_typed_transfer_session_tree tree = Some result).
    {
      unfold phase1_surface_normalize_typed_transfer_session_tree.
      unfold phase1_surface_normalize_transfer_refined_session_tree.
      rewrite Hsession.
      cbn.
      rewrite Hlift.
      cbn.
      exact Htyped_nonreference.
    }
    exists result.
    split.
    + exact Hresult.
    + eapply phase1_surface_normalize_typed_transfer_session_tree_round_trip.
      exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      let session := constr:(Phase1StaticReferenceSessionSpine selected) in
      let middle := constr:(Phase1TransferRefinedStaticReferenceSession selected) in
      let result := constr:(Phase1TypedTransferStaticReferenceSession selected) in
      assert (Hsession :
        phase1_surface_normalize_session_spine tree = Some session).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_session_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        reflexivity.
      }
      assert (Hmiddle :
        phase1_surface_normalize_transfer_refined_session_tree tree = Some middle).
      {
        unfold phase1_surface_normalize_transfer_refined_session_tree.
        rewrite Hsession.
        reflexivity.
      }
      assert (Hresult :
        phase1_surface_normalize_typed_transfer_session_tree tree = Some result).
      {
        unfold phase1_surface_normalize_typed_transfer_session_tree.
        rewrite Hmiddle.
        reflexivity.
      }
      exists result.
      split.
      * exact Hresult.
      * eapply phase1_surface_normalize_typed_transfer_session_tree_round_trip.
        exact Hresult.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
