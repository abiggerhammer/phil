From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStaticArgumentsTotality
  GrammarAstRefinementTupleTypeCarrierTotality.

Import ListNotations.
Open Scope string_scope.

(* Lift static-argument totality through static_reference / named_type / type_expression. *)

Lemma phase1_surface_normalize_static_arguments_reference_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "static_reference")
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_static_reference_spine tree = Some base /\
      phase1_surface_normalize_static_arguments_reference_spine base =
        Some refined /\
      phase1_surface_static_arguments_reference_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "static_reference"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_static_reference_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "static_reference"))
      [ ENonterminal "qualified_name";
        EOptional (ENonterminal "static_arguments")
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  inversion Hitems as
    [| path0 index0 item0 items0 input0 middle0 rest0
       name_tree tail1 Hname Htail1]; subst.
  inversion Htail1 as
    [| path1 index1 item1 items1 input1 middle1 rest1
       arguments_tree nil_trees Harguments Hnil]; subst.
  inversion Hnil; subst.
  destruct
    (phase1_surface_normalize_qualified_name_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules _
      (ENonterminal "static_arguments")
      _ _ arguments_tree Harguments)
    as [[_ Hnone] | [arguments_body [Hsome Harguments_body]]].
  - let base := constr:(
      {| phase1_static_reference_spine_name := name;
         phase1_static_reference_spine_arguments := None |}) in
    let refined := constr:(
      {| phase1_static_arguments_reference_spine_name := name;
         phase1_static_arguments_reference_spine_arguments := None |}) in
    assert (Hbase :
      phase1_surface_normalize_static_reference_spine tree = Some base).
    {
      rewrite Htree, Hsubtree, Hnone.
      unfold phase1_surface_normalize_static_reference_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_normalize_optional_static_arguments,
        phase1_surface_expect_optional.
      cbn.
      rewrite String.eqb_refl.
      rewrite Hname_normalize.
      reflexivity.
    }
    assert (Hrefined :
      phase1_surface_normalize_static_arguments_reference_spine base =
        Some refined).
    { reflexivity. }
    exists base, refined.
    split.
    + exact Hbase.
    + split.
      * exact Hrefined.
      * transitivity (phase1_surface_static_reference_spine_tree base).
        -- eapply
             phase1_surface_normalize_static_arguments_reference_spine_round_trip.
           exact Hrefined.
        -- eapply phase1_surface_normalize_static_reference_spine_round_trip.
           exact Hbase.
  - pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "static_arguments" _ _ _ arguments_body Harguments_body)
      as Hvalidate.
    destruct
      (phase1_surface_normalize_static_arguments_spine_total_from_derivation
        _ _ _ arguments_body Harguments_body)
      as [arguments [Harguments_normalize Harguments_round_trip]].
    let base := constr:(
      {| phase1_static_reference_spine_name := name;
         phase1_static_reference_spine_arguments := Some arguments_body |}) in
    let refined := constr:(
      {| phase1_static_arguments_reference_spine_name := name;
         phase1_static_arguments_reference_spine_arguments := Some arguments |}) in
    assert (Hbase :
      phase1_surface_normalize_static_reference_spine tree = Some base).
    {
      rewrite Htree, Hsubtree, Hsome.
      unfold phase1_surface_normalize_static_reference_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_normalize_optional_static_arguments,
        phase1_surface_expect_optional.
      cbn.
      rewrite String.eqb_refl.
      rewrite Hname_normalize.
      unfold phase1_surface_validate_named_node in Hvalidate |- *.
      rewrite Hvalidate.
      reflexivity.
    }
    assert (Hrefined :
      phase1_surface_normalize_static_arguments_reference_spine base =
        Some refined).
    {
      cbn.
      rewrite Harguments_normalize.
      reflexivity.
    }
    exists base, refined.
    split.
    + exact Hbase.
    + split.
      * exact Hrefined.
      * transitivity (phase1_surface_static_reference_spine_tree base).
        -- eapply
             phase1_surface_normalize_static_arguments_reference_spine_round_trip.
           exact Hrefined.
        -- eapply phase1_surface_normalize_static_reference_spine_round_trip.
           exact Hbase.
Qed.

Theorem phase1_surface_normalize_static_arguments_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "type_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_static_arguments_type_tree tree = Some refined /\
      phase1_surface_static_arguments_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "type_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_type_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "type_expression"))
      phase1_surface_type_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_refinement_tuple_nonreference_total_from_derivation
        (descend
          (descend path (AtNonterminal "type_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [type_value [primitive [shallow [refined
          [Houter [Hprimitive [Hshallow [Hrefine Hround]]]]]]]].
    let outer_type := constr:(Phase1NonreferenceTypeSpine type_value) in
    let primitive_type := constr:(Phase1PrimitiveNonreferenceTypeSpine primitive) in
    let shallow_type := constr:(Phase1ShallowCompoundNonreferenceTypeSpine shallow) in
    let refinement_type := constr:(Phase1RefinementTupleNonreferenceTypeSpine refined) in
    let static_reference_type := constr:(Phase1StaticReferenceNonreferenceType refined) in
    let result := constr:(Phase1StaticArgumentsNonreferenceType refined) in
    assert (Htype :
      phase1_surface_normalize_type_spine tree = Some outer_type).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_type_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite String.eqb_refl.
      rewrite Houter.
      reflexivity.
    }
    assert (Hprimitive_type :
      phase1_surface_normalize_primitive_type_tree tree = Some primitive_type).
    {
      unfold phase1_surface_normalize_primitive_type_tree.
      rewrite Htype.
      cbn.
      rewrite Hprimitive.
      reflexivity.
    }
    assert (Hshallow_type :
      phase1_surface_normalize_shallow_compound_type_tree tree = Some shallow_type).
    {
      unfold phase1_surface_normalize_shallow_compound_type_tree.
      rewrite Hprimitive_type.
      cbn.
      rewrite Hshallow.
      reflexivity.
    }
    assert (Hrefinement_type :
      phase1_surface_normalize_refinement_tuple_type_tree tree =
        Some refinement_type).
    {
      unfold phase1_surface_normalize_refinement_tuple_type_tree.
      rewrite Hshallow_type.
      cbn.
      rewrite Hrefine.
      reflexivity.
    }
    assert (Hstatic_reference_type :
      phase1_surface_normalize_static_reference_type_tree tree =
        Some static_reference_type).
    {
      unfold phase1_surface_normalize_static_reference_type_tree.
      rewrite Hrefinement_type.
      reflexivity.
    }
    assert (Hresult :
      phase1_surface_normalize_static_arguments_type_tree tree = Some result).
    {
      unfold phase1_surface_normalize_static_arguments_type_tree.
      rewrite Hstatic_reference_type.
      reflexivity.
    }
    exists result.
    split.
    + exact Hresult.
    + eapply phase1_surface_normalize_static_arguments_type_tree_round_trip.
      exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules
          (descend
            (descend path (AtNonterminal "type_expression"))
            (AtAlternative 1))
          "named_type" input rest selected Hselected)
        as [named_body [reference_tree
            [Hnamed_lookup [Hnamed_tree Hreference]]]].
      rewrite phase1_surface_named_type_lookup_for_totality in Hnamed_lookup.
      inversion Hnamed_lookup; subst named_body.
      destruct
        (phase1_surface_normalize_static_arguments_reference_layers_total_from_derivation
          _ _ _ reference_tree Hreference)
        as [base_reference [refined_reference
            [Hbase_reference [Hrefined_reference Hreference_round_trip]]]].
      assert (Hnamed :
        phase1_surface_normalize_named_type_spine selected =
          Some base_reference).
      {
        rewrite Hnamed_tree.
        unfold phase1_surface_normalize_named_type_spine,
          phase1_surface_expect_nonterminal.
        cbn.
        rewrite String.eqb_refl.
        exact Hbase_reference.
      }
      let outer_type := constr:(Phase1NamedTypeSpine selected) in
      let primitive_type := constr:(Phase1PrimitiveNamedTypeSpine selected) in
      let shallow_type := constr:(Phase1ShallowCompoundNamedTypeSpine selected) in
      let refinement_type := constr:(Phase1RefinementTupleNamedTypeSpine selected) in
      let static_reference_type := constr:(Phase1StaticReferenceNamedType base_reference) in
      let result := constr:(Phase1StaticArgumentsNamedType refined_reference) in
      assert (Htype :
        phase1_surface_normalize_type_spine tree = Some outer_type).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_type_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite String.eqb_refl.
        reflexivity.
      }
      assert (Hprimitive_type :
        phase1_surface_normalize_primitive_type_tree tree = Some primitive_type).
      {
        unfold phase1_surface_normalize_primitive_type_tree.
        rewrite Htype.
        reflexivity.
      }
      assert (Hshallow_type :
        phase1_surface_normalize_shallow_compound_type_tree tree = Some shallow_type).
      {
        unfold phase1_surface_normalize_shallow_compound_type_tree.
        rewrite Hprimitive_type.
        reflexivity.
      }
      assert (Hrefinement_type :
        phase1_surface_normalize_refinement_tuple_type_tree tree =
          Some refinement_type).
      {
        unfold phase1_surface_normalize_refinement_tuple_type_tree.
        rewrite Hshallow_type.
        reflexivity.
      }
      assert (Hstatic_reference_type :
        phase1_surface_normalize_static_reference_type_tree tree =
          Some static_reference_type).
      {
        unfold phase1_surface_normalize_static_reference_type_tree.
        rewrite Hrefinement_type.
        cbn.
        rewrite Hnamed.
        reflexivity.
      }
      assert (Hresult :
        phase1_surface_normalize_static_arguments_type_tree tree = Some result).
      {
        unfold phase1_surface_normalize_static_arguments_type_tree.
        rewrite Hstatic_reference_type.
        cbn.
        rewrite Hrefined_reference.
        reflexivity.
      }
      exists result.
      split.
      * exact Hresult.
      * eapply phase1_surface_normalize_static_arguments_type_tree_round_trip.
        exact Hresult.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
