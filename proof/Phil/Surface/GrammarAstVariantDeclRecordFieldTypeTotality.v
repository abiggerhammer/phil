From Phil.Surface Require Import
  GrammarAstVariantDeclRecordFieldTypeSpine
  GrammarAstVariantRecordFieldTypeTotality
  GrammarAstDataTotality.

(*
  Compose the staged variant normalizers into a raw-tree adapter, then prove
  derivation-driven totality for the record-field-type-refined variant_decl.
*)

Definition phase1_surface_normalize_record_field_type_variant_tree
  (tree : ParseTree) : option Phase1SurfaceRecordFieldTypeVariantSpine :=
  match phase1_surface_normalize_variant_spine tree with
  | Some base =>
      match phase1_surface_normalize_variant_payload_variant_spine base with
      | Some payload_refined =>
          phase1_surface_normalize_record_field_type_variant_spine payload_refined
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_record_field_type_variant_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_record_field_type_variant_tree tree = Some refined ->
    phase1_surface_record_field_type_variant_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_record_field_type_variant_tree in Hnormalize.
  destruct (phase1_surface_normalize_variant_spine tree)
    as [base |] eqn:Hbase; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_variant_payload_variant_spine base)
    as [payload_refined |] eqn:Hpayload; try discriminate Hnormalize.
  transitivity
    (phase1_surface_variant_payload_variant_spine_tree payload_refined).
  - eapply phase1_surface_normalize_record_field_type_variant_spine_round_trip.
    exact Hnormalize.
  - transitivity (phase1_surface_variant_spine_tree base).
    + eapply phase1_surface_normalize_variant_payload_variant_spine_round_trip.
      exact Hpayload.
    + eapply phase1_surface_normalize_variant_spine_round_trip.
      exact Hbase.
Qed.

Theorem phase1_surface_normalize_record_field_type_variant_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "variant_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_field_type_variant_tree tree =
        Some refined /\
      phase1_surface_record_field_type_variant_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "variant_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_variant_decl_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "variant_decl"))
      [ ENonterminal "identifier";
        EOptional (ENonterminal "variant_payload")
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "variant_decl")) 0
      (ENonterminal "identifier")
      [ EOptional (ENonterminal "variant_payload") ]
      input rest trees Hitems)
    as [after_name [name_tree [tail1_trees
      [Htrees [Hname Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "variant_decl")) 1
      (EOptional (ENonterminal "variant_payload")) []
      after_name rest tail1_trees Htail1)
    as [after_payload [payload_tree [nil_trees
      [Htail1_trees [Hpayload Hnil]]]]].
  rewrite Htrees, Htail1_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules _
      (ENonterminal "variant_payload")
      _ _ payload_tree Hpayload)
    as [[_ Hnone] | [payload_body [Hsome Hpayload_body]]].
  - pose (base :=
      {| phase1_variant_spine_name := name;
         phase1_variant_spine_payload := None |}).
    pose (middle :=
      {| phase1_variant_payload_variant_spine_name := name;
         phase1_variant_payload_variant_spine_payload := None |}).
    pose (refined :=
      {| phase1_record_field_type_variant_spine_name := name;
         phase1_record_field_type_variant_spine_payload := None |}).
    assert (Hbase :
      phase1_surface_normalize_variant_spine tree = Some base).
    {
      rewrite Htree, Hsubtree, Hnone.
      unfold phase1_surface_normalize_variant_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_normalize_optional_variant_payload,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hname_normalize.
      unfold base.
      reflexivity.
    }
    assert (Hmiddle :
      phase1_surface_normalize_variant_payload_variant_spine base =
        Some middle).
    {
      unfold base, middle.
      reflexivity.
    }
    assert (Hrefined :
      phase1_surface_normalize_record_field_type_variant_spine middle =
        Some refined).
    {
      unfold middle, refined.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_record_field_type_variant_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_record_field_type_variant_tree.
      rewrite Hbase, Hmiddle.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_record_field_type_variant_tree_round_trip.
      exact Hnormalize.
  - pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "variant_payload" _ _ _ payload_body Hpayload_body)
      as Hpayload_validate.
    destruct
      (phase1_surface_normalize_variant_payload_spine_total_from_derivation
        _ _ _ payload_body Hpayload_body)
      as [payload [Hpayload_normalize Hpayload_round_trip]].
    destruct
      (phase1_surface_normalize_record_field_type_variant_payload_tree_total_from_derivation
        _ _ _ payload_body Hpayload_body)
      as [payload_refined [Hpayload_refined_tree Hpayload_refined_round_trip]].
    assert (Hpayload_refined :
      phase1_surface_normalize_record_field_type_variant_payload_spine payload =
        Some payload_refined).
    {
      unfold
        phase1_surface_normalize_record_field_type_variant_payload_tree
        in Hpayload_refined_tree.
      rewrite Hpayload_normalize in Hpayload_refined_tree.
      exact Hpayload_refined_tree.
    }
    pose (base :=
      {| phase1_variant_spine_name := name;
         phase1_variant_spine_payload := Some payload_body |}).
    pose (middle :=
      {| phase1_variant_payload_variant_spine_name := name;
         phase1_variant_payload_variant_spine_payload := Some payload |}).
    pose (refined :=
      {| phase1_record_field_type_variant_spine_name := name;
         phase1_record_field_type_variant_spine_payload :=
           Some payload_refined |}).
    assert (Hbase :
      phase1_surface_normalize_variant_spine tree = Some base).
    {
      rewrite Htree, Hsubtree, Hsome.
      unfold phase1_surface_normalize_variant_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_normalize_optional_variant_payload,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hname_normalize.
      rewrite Hpayload_validate.
      unfold base.
      reflexivity.
    }
    assert (Hmiddle :
      phase1_surface_normalize_variant_payload_variant_spine base =
        Some middle).
    {
      unfold phase1_surface_normalize_variant_payload_variant_spine.
      unfold base.
      cbn.
      rewrite Hpayload_normalize.
      unfold middle.
      reflexivity.
    }
    assert (Hrefined :
      phase1_surface_normalize_record_field_type_variant_spine middle =
        Some refined).
    {
      unfold phase1_surface_normalize_record_field_type_variant_spine.
      unfold middle.
      cbn.
      rewrite Hpayload_refined.
      unfold refined.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_record_field_type_variant_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_record_field_type_variant_tree.
      rewrite Hbase, Hmiddle.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_record_field_type_variant_tree_round_trip.
      exact Hnormalize.
Qed.
