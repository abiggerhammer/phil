From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferPayloadSpine
  GrammarAstSessionTotality
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the immediate send/receive session payload shell. *)

Definition phase1_surface_named_annotation_expression_for_totality
  (keyword name : string) : EbnfExpression :=
  EOptional
    (ESequence
      [ ELiteral keyword;
        ENonterminal name
      ]).

Lemma phase1_surface_normalize_optional_named_annotation_total_from_derivation :
  forall keyword name path input rest tree,
    Derives phase1_surface_rules path
      (phase1_surface_named_annotation_expression_for_totality keyword name)
      input rest tree ->
    exists value,
      phase1_surface_normalize_optional_named_annotation keyword name tree =
        Some value /\
      phase1_surface_optional_named_annotation_tree keyword value = tree.
Proof.
  intros keyword name path input rest tree Hderive.
  unfold phase1_surface_named_annotation_expression_for_totality in Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ESequence [ELiteral keyword; ENonterminal name])
      input rest tree Hderive)
    as [[_ Hnone] | [annotation_tree [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_named_annotation keyword name tree =
        Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_named_annotation_round_trip.
      exact Hnormalize.
  - destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtOptionalBody)
        [ ELiteral keyword;
          ENonterminal name
        ]
        input rest annotation_tree Hbody)
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
        (ELiteral keyword) _ _ ?keyword_tree,
      Hvalue : Derives phase1_surface_rules _
        (ENonterminal name) _ _ ?value_tree |- _ =>
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
          as [keyword_tail [_ [_ Hkeyword_tree]]];
        pose proof
          (phase1_surface_validate_named_node_total_from_derivation
            name _ _ _ value_tree Hvalue)
          as Hvalidate;
        assert (Hnormalize :
          phase1_surface_normalize_optional_named_annotation
            keyword name tree = Some (Some value_tree));
        [ rewrite Hsome, Htree, Hkeyword_tree;
          unfold phase1_surface_normalize_optional_named_annotation,
            phase1_surface_expect_optional,
            phase1_surface_expect_sequence,
            phase1_surface_exact2,
            phase1_surface_expect_literal;
          cbn;
          rewrite String.eqb_refl;
          rewrite Hvalidate;
          reflexivity
        | exists (Some value_tree);
          split;
          [ exact Hnormalize
          | eapply phase1_surface_normalize_optional_named_annotation_round_trip;
            exact Hnormalize ] ]
    end.
Qed.

Definition phase1_surface_session_transfer_expression_for_totality
  (direction : Phase1SurfaceSessionTransferDirection) : EbnfExpression :=
  ESequence
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
    ].

Lemma phase1_surface_normalize_session_transfer_spine_total_from_derivation :
  forall direction path input rest tree,
    Derives phase1_surface_rules path
      (phase1_surface_session_transfer_expression_for_totality direction)
      input rest tree ->
    exists transfer,
      phase1_surface_normalize_session_transfer_spine direction tree =
        Some transfer /\
      phase1_surface_session_transfer_spine_tree transfer = tree.
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
      let transfer := constr:(
        {| phase1_session_transfer_direction := direction;
           phase1_session_transfer_parameter_tree := parameter_tree;
           phase1_session_transfer_boundary_tree := boundary;
           phase1_session_transfer_guard_tree := guard;
           phase1_session_transfer_continuation_tree := continuation_tree |}) in
      assert (Hnormalize :
        phase1_surface_normalize_session_transfer_spine direction tree =
          Some transfer);
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
      | exists transfer;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_session_transfer_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Theorem
  phase1_surface_normalize_transfer_refined_nonreference_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_session_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
        Some refined /\
      phase1_surface_transfer_refined_nonreference_session_spine_tree refined =
        tree.
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
      (phase1_surface_normalize_session_transfer_spine_total_from_derivation
        Phase1SessionSend
        (descend
          (descend path (AtNonterminal "nonreference_session_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [transfer [Htransfer Htransfer_round_trip]].
    let base := constr:(
      {| phase1_nonreference_session_spine_tag := Phase1SendSession;
         phase1_nonreference_session_spine_selected_tree := selected |}) in
    let refined := constr:(Phase1RefinedTransferSession transfer) in
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
    assert (Hresult :
      phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
      rewrite Hbase.
      cbn.
      rewrite Htransfer.
      reflexivity.
    }
    exists refined.
    split.
    + exact Hresult.
    + eapply
        phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip.
      exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_session_transfer_spine_total_from_derivation
          Phase1SessionReceive
          (descend
            (descend path (AtNonterminal "nonreference_session_expression"))
            (AtAlternative 1))
          input rest selected Hselected)
        as [transfer [Htransfer Htransfer_round_trip]].
      let base := constr:(
        {| phase1_nonreference_session_spine_tag := Phase1ReceiveSession;
           phase1_nonreference_session_spine_selected_tree := selected |}) in
      let refined := constr:(Phase1RefinedTransferSession transfer) in
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
      assert (Hresult :
        phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
          Some refined).
      {
        unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
        rewrite Hbase.
        cbn.
        rewrite Htransfer.
        reflexivity.
      }
      exists refined.
      split.
      * exact Hresult.
      * eapply
          phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip.
        exact Hresult.
    + destruct index as [|index].
      * cbn in Hnth.
        inversion Hnth; subst item.
        let base := constr:(
          {| phase1_nonreference_session_spine_tag := Phase1SelectSession;
             phase1_nonreference_session_spine_selected_tree := selected |}) in
        let refined := constr:(Phase1OpaqueSelectSession selected) in
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
        assert (Hresult :
          phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
            Some refined).
        {
          unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
          rewrite Hbase.
          reflexivity.
        }
        exists refined.
        split.
        -- exact Hresult.
        -- eapply
             phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip.
           exact Hresult.
      * destruct index as [|index].
        -- cbn in Hnth.
           inversion Hnth; subst item.
           let base := constr:(
             {| phase1_nonreference_session_spine_tag := Phase1OfferSession;
                phase1_nonreference_session_spine_selected_tree := selected |}) in
           let refined := constr:(Phase1OpaqueOfferSession selected) in
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
           assert (Hresult :
             phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
               Some refined).
           {
             unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
             rewrite Hbase.
             reflexivity.
           }
           exists refined.
           split.
           ++ exact Hresult.
           ++ eapply
                phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip.
              exact Hresult.
        -- destruct index as [|index].
           ++ cbn in Hnth.
              inversion Hnth; subst item.
              let base := constr:(
                {| phase1_nonreference_session_spine_tag := Phase1EndSession;
                   phase1_nonreference_session_spine_selected_tree := selected |}) in
              let refined := constr:(Phase1OpaqueEndSession selected) in
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
              assert (Hresult :
                phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
                  Some refined).
              {
                unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
                rewrite Hbase.
                reflexivity.
              }
              exists refined.
              split.
              ** exact Hresult.
              ** eapply
                   phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip.
                 exact Hresult.
           ++ destruct index as [|index].
              ** cbn in Hnth.
                 inversion Hnth; subst item.
                 let base := constr:(
                   {| phase1_nonreference_session_spine_tag := Phase1RecursiveSession;
                      phase1_nonreference_session_spine_selected_tree := selected |}) in
                 let refined := constr:(Phase1OpaqueRecursiveSession selected) in
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
                 assert (Hresult :
                   phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
                     Some refined).
                 {
                   unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
                   rewrite Hbase.
                   reflexivity.
                 }
                 exists refined.
                 split.
                 --- exact Hresult.
                 --- eapply
                      phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip.
                     exact Hresult.
              ** destruct index as [|index].
                 --- cbn in Hnth.
                     inversion Hnth; subst item.
                     let base := constr:(
                       {| phase1_nonreference_session_spine_tag := Phase1ContinueSession;
                          phase1_nonreference_session_spine_selected_tree := selected |}) in
                     let refined := constr:(Phase1OpaqueContinueSession selected) in
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
                     assert (Hresult :
                       phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
                         Some refined).
                     {
                       unfold phase1_surface_normalize_transfer_refined_nonreference_session_tree.
                       rewrite Hbase.
                       reflexivity.
                     }
                     exists refined.
                     split.
                     +++ exact Hresult.
                     +++ eapply
                          phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip.
                         exact Hresult.
                 --- cbn in Hnth.
                     discriminate Hnth.
Qed.
