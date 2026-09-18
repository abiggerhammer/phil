From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericKindTypeSpine
  GrammarAstGenericParamsTotality
  GrammarAstStaticTypeArgumentCarrierTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the typed generic-kind payload refinement from #1188. *)

Lemma phase1_surface_normalize_typed_generic_kind_type_total_from_derivation :
  forall keyword path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral keyword; ENonterminal "type_expression"])
      input rest tree ->
    exists type_value,
      phase1_surface_normalize_typed_generic_kind_type keyword tree =
        Some type_value /\
      PTSequence
        [ PTLiteral keyword;
          phase1_surface_static_type_arguments_type_spine_tree type_value
        ] = tree.
Proof.
  intros keyword path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral keyword;
        ENonterminal "type_expression"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral keyword)
      [ ENonterminal "type_expression" ]
      input rest trees Hitems)
    as [middle [keyword_tree [tail_trees
      [Htrees [Hkeyword Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "type_expression") []
      middle rest tail_trees Htail)
    as [final [type_tree [nil_trees
      [Htail_trees [Htype Hnil]]]]].
  rewrite Htrees, Htail_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (phase1_surface_normalize_static_type_arguments_type_tree_total_from_derivation
      _ _ _ type_tree Htype)
    as [type_value [Htype_normalize Htype_round_trip]].
  assert (Hnormalize :
    phase1_surface_normalize_typed_generic_kind_type keyword tree =
      Some type_value).
  {
    rewrite Htree, Hkeyword_tree.
    unfold phase1_surface_normalize_typed_generic_kind_type,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite String.eqb_refl.
    rewrite Htype_normalize.
    reflexivity.
  }
  exists type_value.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_typed_generic_kind_type_round_trip.
    exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_generic_kind_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_kind")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined /\
      phase1_surface_generic_kind_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_kind"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_kind_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "generic_kind"))
      phase1_surface_generic_kind_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct
    (phase1_surface_generic_kind_item_matches_tag index item Hnth)
    as [tag [Htag Hitem]].
  subst item.
  pose proof
    (phase1_surface_validate_generic_kind_selected_total_from_derivation
      tag
      (descend
        (descend path (AtNonterminal "generic_kind"))
        (AtAlternative index))
      input rest selected Hselected) as Hvalidate.
  pose (base :=
    {| phase1_generic_kind_spine_tag := tag;
       phase1_generic_kind_spine_selected_tree := selected |}).
  assert (Hbase :
    phase1_surface_normalize_generic_kind_spine tree = Some base).
  {
    rewrite Htree, Hsubtree.
    unfold phase1_surface_normalize_generic_kind_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn.
    rewrite Htag, Hvalidate.
    reflexivity.
  }
  destruct tag.
  - pose (refined := Phase1GenericTypeKind).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericNatKind).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericSessionKind).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericMessageKind).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericEffectsKind).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type_total_from_derivation
        "provider" _ _ _ selected Hselected)
      as [type_value [Htype Htype_round_trip]].
    pose (refined := Phase1GenericProviderKind type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htype.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type_total_from_derivation
        "callable" _ _ _ selected Hselected)
      as [type_value [Htype Htype_round_trip]].
    pose (refined := Phase1GenericCallableKind type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htype.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type_total_from_derivation
        "boundary" _ _ _ selected Hselected)
      as [type_value [Htype Htype_round_trip]].
    pose (refined := Phase1GenericBoundaryKind type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htype.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type_total_from_derivation
        "architecture" _ _ _ selected Hselected)
      as [type_value [Htype Htype_round_trip]].
    pose (refined := Phase1GenericArchitectureKind type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_kind_type_spine base = Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htype.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_kind_type_tree tree = Some refined).
    {
      unfold phase1_surface_normalize_generic_kind_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_kind_type_tree_round_trip.
      exact Hnormalize.
Qed.
