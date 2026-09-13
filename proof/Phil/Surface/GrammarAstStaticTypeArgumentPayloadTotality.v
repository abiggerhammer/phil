From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStaticTypeArgumentPayloadSpine
  GrammarAstStaticArgumentsTotality
  GrammarAstRefinementTupleTypeCarrierTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the type-valued static_argument payload refinement from #988. *)

Lemma phase1_surface_normalize_complete_nonreference_type_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    exists refined,
      phase1_surface_normalize_complete_nonreference_type_spine tree =
        Some refined /\
      phase1_surface_refinement_tuple_nonreference_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_refinement_tuple_nonreference_total_from_derivation
      path input rest tree Hderive)
    as [outer [primitive [shallow [refined
        [Houter [Hprimitive [Hshallow [Hrefine Hround]]]]]]]].
  exists refined.
  split.
  - unfold phase1_surface_normalize_complete_nonreference_type_spine.
    rewrite Houter.
    rewrite Hprimitive.
    rewrite Hshallow.
    exact Hrefine.
  - exact Hround.
Qed.

Theorem phase1_surface_normalize_static_type_argument_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "static_argument")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_static_type_argument_tree tree = Some refined /\
      phase1_surface_static_type_argument_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "static_argument"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_static_argument_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "static_argument"))
      phase1_surface_static_argument_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "nonreference_type_expression" _ _ _ selected Hselected)
      as Hvalidate.
    destruct
      (phase1_surface_normalize_complete_nonreference_type_spine_total_from_derivation
        _ _ _ selected Hselected)
      as [type_value [Htype Htype_round_trip]].
    let base := constr:(
      {| phase1_static_argument_spine_tag := Phase1StaticTypeArgument;
         phase1_static_argument_spine_selected_tree := selected |}) in
    let refined := constr:(Phase1StaticRefinedTypeArgument type_value) in
    assert (Hbase :
      phase1_surface_normalize_static_argument_spine tree = Some base).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_static_argument_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative,
        phase1_surface_validate_static_argument_selected,
        phase1_surface_static_argument_tag_name.
      cbn.
      rewrite Hvalidate.
      reflexivity.
    }
    assert (Hrefined :
      phase1_surface_normalize_static_type_argument_spine base = Some refined).
    {
      cbn.
      rewrite Htype.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_static_type_argument_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_static_type_argument_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_static_type_argument_tree_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "nonreference_session_expression" _ _ _ selected Hselected)
        as Hvalidate.
      let base := constr:(
        {| phase1_static_argument_spine_tag := Phase1StaticSessionArgument;
           phase1_static_argument_spine_selected_tree := selected |}) in
      let refined := constr:(Phase1StaticOpaqueSessionArgument selected) in
      assert (Hbase :
        phase1_surface_normalize_static_argument_spine tree = Some base).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_static_argument_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative,
          phase1_surface_validate_static_argument_selected,
          phase1_surface_static_argument_tag_name.
        cbn.
        rewrite Hvalidate.
        reflexivity.
      }
      assert (Hnormalize :
        phase1_surface_normalize_static_type_argument_tree tree = Some refined).
      {
        unfold phase1_surface_normalize_static_type_argument_tree.
        rewrite Hbase.
        reflexivity.
      }
      exists refined.
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_static_type_argument_tree_round_trip.
        exact Hnormalize.
    + destruct index as [|index].
      * cbn in Hnth.
        inversion Hnth; subst item.
        pose proof
          (phase1_surface_validate_named_node_total_from_derivation
            "static_value_expression" _ _ _ selected Hselected)
          as Hvalidate.
        let base := constr:(
          {| phase1_static_argument_spine_tag := Phase1StaticValueArgument;
             phase1_static_argument_spine_selected_tree := selected |}) in
        let refined := constr:(Phase1StaticOpaqueValueArgument selected) in
        assert (Hbase :
          phase1_surface_normalize_static_argument_spine tree = Some base).
        {
          rewrite Htree, Hsubtree.
          unfold phase1_surface_normalize_static_argument_spine,
            phase1_surface_expect_nonterminal,
            phase1_surface_expect_alternative,
            phase1_surface_validate_static_argument_selected,
            phase1_surface_static_argument_tag_name.
          cbn.
          rewrite Hvalidate.
          reflexivity.
        }
        assert (Hnormalize :
          phase1_surface_normalize_static_type_argument_tree tree = Some refined).
        {
          unfold phase1_surface_normalize_static_type_argument_tree.
          rewrite Hbase.
          reflexivity.
        }
        exists refined.
        split.
        -- exact Hnormalize.
        -- eapply phase1_surface_normalize_static_type_argument_tree_round_trip.
           exact Hnormalize.
      * destruct index as [|index].
        -- cbn in Hnth.
           inversion Hnth; subst item.
           pose proof
             (phase1_surface_validate_named_node_total_from_derivation
               "effect_set_literal" _ _ _ selected Hselected)
             as Hvalidate.
           let base := constr:(
             {| phase1_static_argument_spine_tag := Phase1StaticEffectSetArgument;
                phase1_static_argument_spine_selected_tree := selected |}) in
           let refined := constr:(Phase1StaticOpaqueEffectSetArgument selected) in
           assert (Hbase :
             phase1_surface_normalize_static_argument_spine tree = Some base).
           {
             rewrite Htree, Hsubtree.
             unfold phase1_surface_normalize_static_argument_spine,
               phase1_surface_expect_nonterminal,
               phase1_surface_expect_alternative,
               phase1_surface_validate_static_argument_selected,
               phase1_surface_static_argument_tag_name.
             cbn.
             rewrite Hvalidate.
             reflexivity.
           }
           assert (Hnormalize :
             phase1_surface_normalize_static_type_argument_tree tree =
               Some refined).
           {
             unfold phase1_surface_normalize_static_type_argument_tree.
             rewrite Hbase.
             reflexivity.
           }
           exists refined.
           split.
           ++ exact Hnormalize.
           ++ eapply phase1_surface_normalize_static_type_argument_tree_round_trip.
              exact Hnormalize.
        -- cbn in Hnth.
           discriminate Hnth.
Qed.
