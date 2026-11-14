From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSourceHeader
  GrammarAstSourceHeaderTotality
  GrammarAstVariantPayloadSpine
  GrammarAstVariantRecordFieldTypeSpine
  GrammarAstRecordFieldsTotality
  GrammarAstOptionalFieldTypeTotality
  GrammarAstDataTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the record-shaped variant payload refinement from #1176. *)

Lemma
  phase1_surface_normalize_record_field_type_variant_record_selected_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_record_variant_payload_expression_for_totality
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_record_variant_payload_selected tree = Some base /\
      phase1_surface_normalize_record_field_type_variant_payload_spine base =
        Some refined /\
      phase1_surface_record_field_type_variant_payload_selected_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_record_variant_payload_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral "{")
      [ phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}" ]
      input rest trees Hitems)
    as [after_open [open_tree [tail1_trees
      [Htrees [Hopen Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      phase1_surface_optional_fields_expression_for_totality
      [ELiteral "}"]
      after_open rest tail1_trees Htail1)
    as [after_fields [fields_tree [tail2_trees
      [Htail1_trees [Hfields Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (ELiteral "}") []
      after_fields rest tail2_trees Htail2)
    as [after_close [close_tree [nil_trees
      [Htail2_trees [Hclose Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "{" _ _ open_tree Hopen)
    as [open_tail [_ [_ Hopen_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "}" _ _ close_tree Hclose)
    as [close_tail [_ [_ Hclose_tree]]].
  destruct
    (phase1_surface_normalize_optional_field_type_tree_total_from_derivation
      _ _ _ fields_tree Hfields)
    as [base_fields [refined_fields
      [Hbase_fields [Hrefined_fields Hrefined_fields_tree]]]].
  pose (base := Phase1VariantRecordPayloadSpine base_fields).
  pose (refined :=
    Phase1RecordFieldTypeVariantRecordPayloadSpine refined_fields).
  assert (Hbase :
    phase1_surface_normalize_record_variant_payload_selected tree =
      Some base).
  {
    rewrite Htree, Hopen_tree, Hclose_tree.
    unfold phase1_surface_normalize_record_variant_payload_selected,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hbase_fields.
    reflexivity.
  }
  assert (Hrefined :
    phase1_surface_normalize_record_field_type_variant_payload_spine
      base = Some refined).
  {
    unfold base, refined.
    cbn.
    rewrite Hrefined_fields.
    reflexivity.
  }
  exists base, refined.
  split.
  - exact Hbase.
  - split.
    + exact Hrefined.
    + unfold refined.
      rewrite Htree, Hopen_tree, Hclose_tree.
      change
        (PTSequence
          [ PTLiteral "{";
            phase1_surface_optional_field_type_list_tree refined_fields;
            PTLiteral "}" ]) =
        (PTSequence
          [ PTLiteral "{";
            fields_tree;
            PTLiteral "}" ]).
      rewrite Hrefined_fields_tree.
      reflexivity.
Qed.

Lemma
  phase1_surface_normalize_record_field_type_variant_tuple_selected_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_tuple_variant_payload_expression_for_totality
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_tuple_variant_payload_selected tree = Some base /\
      phase1_surface_normalize_record_field_type_variant_payload_spine base =
        Some refined /\
      phase1_surface_record_field_type_variant_payload_selected_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_tuple_variant_payload_selected_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase [Hindex Hround_trip]]].
  destruct base as [fields | types].
  - discriminate Hindex.
  - exists (Phase1VariantTuplePayloadSpine types),
      (Phase1RecordFieldTypeVariantTuplePayloadSpine types).
    split.
    + exact Hbase.
    + split.
      * reflexivity.
      * exact Hround_trip.
Qed.

Theorem
  phase1_surface_normalize_record_field_type_variant_payload_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "variant_payload")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_field_type_variant_payload_tree tree =
        Some refined /\
      phase1_surface_record_field_type_variant_payload_spine_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "variant_payload"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_variant_payload_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "variant_payload"))
      phase1_surface_variant_payload_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_record_field_type_variant_record_selected_total_from_derivation
        _ _ _ selected Hselected)
      as [base [refined [Hbase Hrefined]]].
    destruct Hrefined as [Hrefined Hselected_round].
    assert (Hbase_tree :
      phase1_surface_normalize_variant_payload_spine tree = Some base).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_variant_payload_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hbase.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_record_field_type_variant_payload_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_record_field_type_variant_payload_tree.
      rewrite Hbase_tree.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_record_field_type_variant_payload_tree_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_record_field_type_variant_tuple_selected_total_from_derivation
          _ _ _ selected Hselected)
        as [base [refined [Hbase [Hrefined Hselected_round]]]].
      assert (Hbase_tree :
        phase1_surface_normalize_variant_payload_spine tree = Some base).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_variant_payload_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite Hbase.
        reflexivity.
      }
      assert (Hnormalize :
        phase1_surface_normalize_record_field_type_variant_payload_tree tree =
          Some refined).
      {
        unfold phase1_surface_normalize_record_field_type_variant_payload_tree.
        rewrite Hbase_tree.
        exact Hrefined.
      }
      exists refined.
      split.
      * exact Hnormalize.
      * eapply
          phase1_surface_normalize_record_field_type_variant_payload_tree_round_trip.
        exact Hnormalize.
    + destruct index; cbn in Hnth; discriminate Hnth.
Qed.
