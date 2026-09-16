From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionTransferBoundaryCarrierSpine
  GrammarAstSessionTransferParamCarrierTotality
  GrammarAstSessionTransferPayloadTotality
  GrammarAstStaticTypeArgumentCarrierTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the boundary-refined transfer/session carrier lift. *)

Lemma phase1_surface_normalize_optional_boundary_reference_total_from_derivation :
  forall path input rest tree boundary,
    Derives phase1_surface_rules path
      (phase1_surface_named_annotation_expression_for_totality
        "using" "static_reference")
      input rest tree ->
    phase1_surface_optional_named_annotation_tree "using" boundary = tree ->
    exists refined,
      phase1_surface_normalize_optional_boundary_reference boundary = Some refined.
Proof.
  intros path input rest tree [reference_tree |] Hderive Htree.
  - rewrite <- Htree in Hderive.
    unfold phase1_surface_named_annotation_expression_for_totality in Hderive.
    destruct
      (optional_derivation_exposes_presence
        phase1_surface_rules path
        (ESequence [ELiteral "using"; ENonterminal "static_reference"])
        input rest
        (phase1_surface_optional_named_annotation_tree
          "using" (Some reference_tree))
        Hderive)
      as [[_ Hnone] | [annotation_tree [Hsome Hbody]]].
    + cbn in Hnone.
      discriminate Hnone.
    + cbn in Hsome.
      inversion Hsome; subst annotation_tree.
      destruct
        (derives_sequence_expression_exposes_items
          phase1_surface_rules
          (descend path AtOptionalBody)
          [ ELiteral "using";
            ENonterminal "static_reference"
          ]
          input rest
          (PTSequence [PTLiteral "using"; reference_tree])
          Hbody)
        as [trees [Hsequence Hitems]].
      cbn in Hsequence.
      inversion Hsequence; subst trees.
      repeat match goal with
      | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
          inversion Hseq; subst; clear Hseq
      end.
      match goal with
      | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
          inversion Hnil; subst; clear Hnil
      end.
      match goal with
      | Hreference : Derives phase1_surface_rules _
          (ENonterminal "static_reference") _ _ reference_tree |- _ =>
          destruct
            (phase1_surface_normalize_static_type_arguments_reference_layers_total_from_derivation
              _ _ _ reference_tree Hreference)
            as [base [middle [refined
                [Hbase [Hmiddle [Hrefined Hrefined_tree]]]]]];
          assert (Hreference_normalize :
            phase1_surface_normalize_static_type_arguments_reference_tree
              reference_tree = Some refined);
          [ unfold phase1_surface_normalize_static_type_arguments_reference_tree;
            rewrite Hbase, Hmiddle;
            exact Hrefined
          | exists (Some refined);
            cbn;
            rewrite Hreference_normalize;
            reflexivity ]
      end.
  - exists None.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_boundary_refined_typed_session_transfer_spine_total_from_derivation :
  forall direction path input rest tree transfer,
    Derives phase1_surface_rules path
      (phase1_surface_session_transfer_expression_for_totality direction)
      input rest tree ->
    phase1_surface_typed_session_transfer_spine_tree transfer = tree ->
    phase1_typed_session_transfer_direction transfer = direction ->
    exists refined,
      phase1_surface_normalize_boundary_refined_typed_session_transfer_spine
        transfer = Some refined.
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
  | Hboundary : Derives phase1_surface_rules _
      (phase1_surface_named_annotation_expression_for_totality
        "using" "static_reference")
      _ _ (phase1_surface_optional_named_annotation_tree "using" boundary) |- _ =>
      destruct
        (phase1_surface_normalize_optional_boundary_reference_total_from_derivation
          _ _ _
          (phase1_surface_optional_named_annotation_tree "using" boundary)
          boundary Hboundary eq_refl)
        as [refined_boundary Hrefined_boundary];
      cbn;
      rewrite Hrefined_boundary;
      eexists;
      reflexivity
  end.
Qed.

Lemma
  phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine_total_from_derivation :
  forall path input rest tree session,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_session_expression")
      input rest tree ->
    phase1_surface_typed_transfer_nonreference_session_spine_tree session = tree ->
    exists refined,
      phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine
        session = Some refined.
Proof.
  intros path input rest tree session Hderive Htree.
  destruct session as
    [transfer | selected | selected | selected | selected | selected].
  - destruct transfer as [direction parameter boundary guard continuation].
    destruct direction.
    + cbn in Htree.
      rewrite <- Htree in Hderive.
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules path "nonreference_session_expression"
          input rest
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative 0
              (phase1_surface_typed_session_transfer_spine_tree
                {| phase1_typed_session_transfer_direction := Phase1SessionSend;
                   phase1_typed_session_transfer_parameter := parameter;
                   phase1_typed_session_transfer_boundary_tree := boundary;
                   phase1_typed_session_transfer_guard_tree := guard;
                   phase1_typed_session_transfer_continuation_tree := continuation |})))
          Hderive)
        as [body [subtree [Hlookup [Hnode Hbody]]]].
      rewrite phase1_surface_nonreference_session_lookup_for_totality in Hlookup.
      inversion Hlookup; subst body.
      cbn in Hnode.
      inversion Hnode; subst subtree.
      destruct
        (alternative_derivation_names_exact_branch
          phase1_surface_rules
          (descend path (AtNonterminal "nonreference_session_expression"))
          phase1_surface_nonreference_session_items_for_totality
          input rest
          (PTAlternative 0
            (phase1_surface_typed_session_transfer_spine_tree
              {| phase1_typed_session_transfer_direction := Phase1SessionSend;
                 phase1_typed_session_transfer_parameter := parameter;
                 phase1_typed_session_transfer_boundary_tree := boundary;
                 phase1_typed_session_transfer_guard_tree := guard;
                 phase1_typed_session_transfer_continuation_tree := continuation |}))
          Hbody)
        as [index [item [actual_selected
            [Hnth [Hselected_tree Hselected]]]]].
      destruct index as [|index].
      * cbn in Hnth.
        inversion Hnth; subst item.
        cbn in Hselected_tree.
        inversion Hselected_tree; subst actual_selected.
        destruct
          (phase1_surface_normalize_boundary_refined_typed_session_transfer_spine_total_from_derivation
            Phase1SessionSend
            (descend
              (descend path (AtNonterminal "nonreference_session_expression"))
              (AtAlternative 0))
            input rest
            (phase1_surface_typed_session_transfer_spine_tree
              {| phase1_typed_session_transfer_direction := Phase1SessionSend;
                 phase1_typed_session_transfer_parameter := parameter;
                 phase1_typed_session_transfer_boundary_tree := boundary;
                 phase1_typed_session_transfer_guard_tree := guard;
                 phase1_typed_session_transfer_continuation_tree := continuation |})
            {| phase1_typed_session_transfer_direction := Phase1SessionSend;
               phase1_typed_session_transfer_parameter := parameter;
               phase1_typed_session_transfer_boundary_tree := boundary;
               phase1_typed_session_transfer_guard_tree := guard;
               phase1_typed_session_transfer_continuation_tree := continuation |}
            Hselected eq_refl eq_refl)
          as [refined Hrefined].
        exists (Phase1BoundaryRefinedTypedTransferSession refined).
        cbn.
        rewrite Hrefined.
        reflexivity.
      * cbn in Hselected_tree.
        discriminate Hselected_tree.
    + cbn in Htree.
      rewrite <- Htree in Hderive.
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules path "nonreference_session_expression"
          input rest
          (PTNonterminal "nonreference_session_expression"
            (PTAlternative 1
              (phase1_surface_typed_session_transfer_spine_tree
                {| phase1_typed_session_transfer_direction := Phase1SessionReceive;
                   phase1_typed_session_transfer_parameter := parameter;
                   phase1_typed_session_transfer_boundary_tree := boundary;
                   phase1_typed_session_transfer_guard_tree := guard;
                   phase1_typed_session_transfer_continuation_tree := continuation |})))
          Hderive)
        as [body [subtree [Hlookup [Hnode Hbody]]]].
      rewrite phase1_surface_nonreference_session_lookup_for_totality in Hlookup.
      inversion Hlookup; subst body.
      cbn in Hnode.
      inversion Hnode; subst subtree.
      destruct
        (alternative_derivation_names_exact_branch
          phase1_surface_rules
          (descend path (AtNonterminal "nonreference_session_expression"))
          phase1_surface_nonreference_session_items_for_totality
          input rest
          (PTAlternative 1
            (phase1_surface_typed_session_transfer_spine_tree
              {| phase1_typed_session_transfer_direction := Phase1SessionReceive;
                 phase1_typed_session_transfer_parameter := parameter;
                 phase1_typed_session_transfer_boundary_tree := boundary;
                 phase1_typed_session_transfer_guard_tree := guard;
                 phase1_typed_session_transfer_continuation_tree := continuation |}))
          Hbody)
        as [index [item [actual_selected
            [Hnth [Hselected_tree Hselected]]]]].
      destruct index as [|index].
      * cbn in Hselected_tree.
        discriminate Hselected_tree.
      * destruct index as [|index].
        -- cbn in Hnth.
           inversion Hnth; subst item.
           cbn in Hselected_tree.
           inversion Hselected_tree; subst actual_selected.
           destruct
             (phase1_surface_normalize_boundary_refined_typed_session_transfer_spine_total_from_derivation
               Phase1SessionReceive
               (descend
                 (descend path (AtNonterminal "nonreference_session_expression"))
                 (AtAlternative 1))
               input rest
               (phase1_surface_typed_session_transfer_spine_tree
                 {| phase1_typed_session_transfer_direction := Phase1SessionReceive;
                    phase1_typed_session_transfer_parameter := parameter;
                    phase1_typed_session_transfer_boundary_tree := boundary;
                    phase1_typed_session_transfer_guard_tree := guard;
                    phase1_typed_session_transfer_continuation_tree := continuation |})
               {| phase1_typed_session_transfer_direction := Phase1SessionReceive;
                  phase1_typed_session_transfer_parameter := parameter;
                  phase1_typed_session_transfer_boundary_tree := boundary;
                  phase1_typed_session_transfer_guard_tree := guard;
                  phase1_typed_session_transfer_continuation_tree := continuation |}
               Hselected eq_refl eq_refl)
             as [refined Hrefined].
           exists (Phase1BoundaryRefinedTypedTransferSession refined).
           cbn.
           rewrite Hrefined.
           reflexivity.
        -- cbn in Hselected_tree.
           discriminate Hselected_tree.
  - exists (Phase1BoundaryRefinedTypedOpaqueSelectSession selected).
    reflexivity.
  - exists (Phase1BoundaryRefinedTypedOpaqueOfferSession selected).
    reflexivity.
  - exists (Phase1BoundaryRefinedTypedOpaqueEndSession selected).
    reflexivity.
  - exists (Phase1BoundaryRefinedTypedOpaqueRecursiveSession selected).
    reflexivity.
  - exists (Phase1BoundaryRefinedTypedOpaqueContinueSession selected).
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_session_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree
        tree = Some refined /\
      phase1_surface_boundary_refined_typed_transfer_nonreference_session_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_typed_transfer_nonreference_session_tree_total_from_derivation
      path input rest tree Hderive)
    as [session [Hsession Hsession_tree]].
  destruct
    (phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine_total_from_derivation
      path input rest tree session Hderive Hsession_tree)
    as [refined Hrefined].
  assert (Hresult :
    phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree
      tree = Some refined).
  {
    unfold
      phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree.
    rewrite Hsession.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_tree_round_trip.
    exact Hresult.
Qed.

Lemma
  phase1_surface_normalize_boundary_refined_typed_transfer_session_spine_total_from_derivation :
  forall path input rest tree session,
    Derives phase1_surface_rules path (ENonterminal "session_expression")
      input rest tree ->
    phase1_surface_typed_transfer_session_spine_tree session = tree ->
    exists refined,
      phase1_surface_normalize_boundary_refined_typed_transfer_session_spine
        session = Some refined.
Proof.
  intros path input rest tree session Hderive Htree.
  destruct session as [nonreference | reference_tree].
  - cbn in Htree.
    rewrite <- Htree in Hderive.
    destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules path "session_expression"
        input rest
        (PTNonterminal "session_expression"
          (PTAlternative 0
            (phase1_surface_typed_transfer_nonreference_session_spine_tree
              nonreference)))
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
          (phase1_surface_typed_transfer_nonreference_session_spine_tree
            nonreference))
        Hbody)
      as [index [item [selected [Hnth [Hselected_tree Hselected]]]]].
    destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      cbn in Hselected_tree.
      inversion Hselected_tree; subst selected.
      destruct
        (phase1_surface_normalize_boundary_refined_typed_transfer_nonreference_session_spine_total_from_derivation
          (descend
            (descend path (AtNonterminal "session_expression"))
            (AtAlternative 0))
          input rest
          (phase1_surface_typed_transfer_nonreference_session_spine_tree
            nonreference)
          nonreference Hselected eq_refl)
        as [refined Hrefined].
      exists (Phase1BoundaryRefinedTypedTransferNonreferenceSession refined).
      cbn.
      rewrite Hrefined.
      reflexivity.
    + cbn in Hselected_tree.
      discriminate Hselected_tree.
  - exists (Phase1BoundaryRefinedTypedTransferStaticReferenceSession reference_tree).
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_boundary_refined_typed_transfer_session_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "session_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_boundary_refined_typed_transfer_session_tree tree =
        Some refined /\
      phase1_surface_boundary_refined_typed_transfer_session_spine_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_typed_transfer_session_tree_total_from_derivation
      path input rest tree Hderive)
    as [session [Hsession Hsession_tree]].
  destruct
    (phase1_surface_normalize_boundary_refined_typed_transfer_session_spine_total_from_derivation
      path input rest tree session Hderive Hsession_tree)
    as [refined Hrefined].
  assert (Hresult :
    phase1_surface_normalize_boundary_refined_typed_transfer_session_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_boundary_refined_typed_transfer_session_tree.
    rewrite Hsession.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_boundary_refined_typed_transfer_session_tree_round_trip.
    exact Hresult.
Qed.
