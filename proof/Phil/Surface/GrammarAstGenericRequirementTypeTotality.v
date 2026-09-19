From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementTypeSpine
  GrammarAstGenericRequirementsTotality
  GrammarAstStaticTypeArgumentCarrierTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the generic-requirement type refinement from #1202. *)

Lemma
  phase1_surface_normalize_named_type_requirement_type_total_from_derivation :
  forall keyword path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral keyword;
          ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "type_expression";
          ELiteral ";"
        ])
      input rest tree ->
    exists name_tree type_value,
      phase1_surface_normalize_named_type_requirement_type keyword tree =
        Some (name_tree, type_value).
Proof.
  intros keyword path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral keyword;
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral keyword)
      [ ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression";
        ELiteral ";" ]
      input rest trees Hitems)
    as [after_keyword [keyword_tree [tail1
      [Htrees [Hkeyword Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "identifier")
      [ ELiteral ":";
        ENonterminal "type_expression";
        ELiteral ";" ]
      after_keyword rest tail1 Htail1)
    as [after_name [name_tree [tail2
      [Htail1_trees [Hname Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (ELiteral ":")
      [ ENonterminal "type_expression";
        ELiteral ";" ]
      after_name rest tail2 Htail2)
    as [after_colon [colon_tree [tail3
      [Htail2_trees [Hcolon Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 3
      (ENonterminal "type_expression")
      [ ELiteral ";" ]
      after_colon rest tail3 Htail3)
    as [after_type [type_tree [tail4
      [Htail3_trees [Htype Htail4]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 4
      (ELiteral ";") []
      after_type rest tail4 Htail4)
    as [after_terminator [terminator_tree [nil_trees
      [Htail4_trees [Hterminator Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees,
    Htail4_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
    as [colon_tail [_ [_ Hcolon_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
    as [terminator_tail [_ [_ Hterminator_tree]]].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "identifier" _ _ _ name_tree Hname) as Hname_validate.
  destruct
    (phase1_surface_normalize_static_type_arguments_type_tree_total_from_derivation
      _ _ _ type_tree Htype)
    as [type_value [Htype_normalize Htype_round_trip]].
  exists name_tree, type_value.
  rewrite Htree, Hkeyword_tree, Hcolon_tree, Hterminator_tree.
  unfold phase1_surface_normalize_named_type_requirement_type,
    phase1_surface_expect_sequence,
    phase1_surface_exact5,
    phase1_surface_expect_literal.
  cbn.
  rewrite String.eqb_refl.
  rewrite Hname_validate, Htype_normalize.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_type_only_requirement_type_total_from_derivation :
  forall keyword path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral keyword;
          ENonterminal "type_expression";
          ELiteral ";"
        ])
      input rest tree ->
    exists type_value,
      phase1_surface_normalize_type_only_requirement_type keyword tree =
        Some type_value.
Proof.
  intros keyword path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral keyword;
        ENonterminal "type_expression";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral keyword)
      [ ENonterminal "type_expression";
        ELiteral ";" ]
      input rest trees Hitems)
    as [after_keyword [keyword_tree [tail1
      [Htrees [Hkeyword Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "type_expression")
      [ ELiteral ";" ]
      after_keyword rest tail1 Htail1)
    as [after_type [type_tree [tail2
      [Htail1_trees [Htype Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (ELiteral ";") []
      after_type rest tail2 Htail2)
    as [after_terminator [terminator_tree [nil_trees
      [Htail2_trees [Hterminator Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
    as [terminator_tail [_ [_ Hterminator_tree]]].
  destruct
    (phase1_surface_normalize_static_type_arguments_type_tree_total_from_derivation
      _ _ _ type_tree Htype)
    as [type_value [Htype_normalize Htype_round_trip]].
  exists type_value.
  rewrite Htree, Hkeyword_tree, Hterminator_tree.
  unfold phase1_surface_normalize_type_only_requirement_type,
    phase1_surface_expect_sequence,
    phase1_surface_exact3,
    phase1_surface_expect_literal.
  cbn.
  rewrite String.eqb_refl.
  rewrite Htype_normalize.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_boundary_representation_requirement_type_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral "boundary";
          ELiteral "representation";
          ENonterminal "type_expression";
          ELiteral ";"
        ])
      input rest tree ->
    exists type_value,
      phase1_surface_normalize_boundary_representation_requirement_type tree =
        Some type_value.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "boundary";
        ELiteral "representation";
        ENonterminal "type_expression";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral "boundary")
      [ ELiteral "representation";
        ENonterminal "type_expression";
        ELiteral ";" ]
      input rest trees Hitems)
    as [after_boundary [boundary_tree [tail1
      [Htrees [Hboundary Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ELiteral "representation")
      [ ENonterminal "type_expression";
        ELiteral ";" ]
      after_boundary rest tail1 Htail1)
    as [after_representation [representation_tree [tail2
      [Htail1_trees [Hrepresentation Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (ENonterminal "type_expression")
      [ ELiteral ";" ]
      after_representation rest tail2 Htail2)
    as [after_type [type_tree [tail3
      [Htail2_trees [Htype Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 3
      (ELiteral ";") []
      after_type rest tail3 Htail3)
    as [after_terminator [terminator_tree [nil_trees
      [Htail3_trees [Hterminator Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "boundary" _ _ boundary_tree Hboundary)
    as [boundary_tail [_ [_ Hboundary_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "representation" _ _ representation_tree Hrepresentation)
    as [representation_tail [_ [_ Hrepresentation_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
    as [terminator_tail [_ [_ Hterminator_tree]]].
  destruct
    (phase1_surface_normalize_static_type_arguments_type_tree_total_from_derivation
      _ _ _ type_tree Htype)
    as [type_value [Htype_normalize Htype_round_trip]].
  exists type_value.
  rewrite Htree, Hboundary_tree, Hrepresentation_tree, Hterminator_tree.
  unfold phase1_surface_normalize_boundary_representation_requirement_type,
    phase1_surface_expect_sequence,
    phase1_surface_exact4,
    phase1_surface_expect_literal.
  cbn.
  rewrite Htype_normalize.
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_generic_requirement_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined /\
      phase1_surface_generic_requirement_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_requirement"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_requirement_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirement"))
      phase1_surface_generic_requirement_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct
    (phase1_surface_generic_requirement_item_matches_tag index item Hnth)
    as [tag [Htag Hitem]].
  subst item.
  pose proof
    (phase1_surface_validate_generic_requirement_selected_total_from_derivation
      tag
      (descend
        (descend path (AtNonterminal "generic_requirement"))
        (AtAlternative index))
      input rest selected Hselected) as Hvalidate.
  pose (base :=
    {| phase1_generic_requirement_spine_tag := tag;
       phase1_generic_requirement_spine_selected_tree := selected |}).
  assert (Hbase :
    phase1_surface_normalize_generic_requirement_spine tree = Some base).
  {
    rewrite Htree, Hsubtree.
    unfold phase1_surface_normalize_generic_requirement_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn.
    rewrite Htag, Hvalidate.
    reflexivity.
  }
  destruct tag; cbn in Hselected.
  - pose (refined := Phase1GenericStructuralRequirement selected).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    { unfold base, refined. reflexivity. }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericPropositionRequirement selected).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    { unfold base, refined. reflexivity. }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type_total_from_derivation
        "provider" _ _ _ selected Hselected)
      as [name_tree [type_value Htyped]].
    pose (refined := Phase1GenericProviderRequirement name_tree type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htyped.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type_total_from_derivation
        "callable" _ _ _ selected Hselected)
      as [name_tree [type_value Htyped]].
    pose (refined := Phase1GenericCallableRequirement name_tree type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htyped.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type_total_from_derivation
        "boundary" _ _ _ selected Hselected)
      as [name_tree [type_value Htyped]].
    pose (refined := Phase1GenericBoundaryRequirement name_tree type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htyped.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type_total_from_derivation
        "architecture" _ _ _ selected Hselected)
      as [name_tree [type_value Htyped]].
    pose (refined := Phase1GenericArchitectureRequirement name_tree type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htyped.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericEffectsRequirement selected).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    { unfold base, refined. reflexivity. }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_type_only_requirement_type_total_from_derivation
        "authority" _ _ _ selected Hselected)
      as [type_value Htyped].
    pose (refined := Phase1GenericAuthorityRequirement type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htyped.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_boundary_representation_requirement_type_total_from_derivation
        _ _ _ selected Hselected)
      as [type_value Htyped].
    pose (refined := Phase1GenericBoundaryRepresentationRequirement type_value).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    {
      unfold base, refined.
      cbn.
      rewrite Htyped.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericRepresentationRequirement selected).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    { unfold base, refined. reflexivity. }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericPlacementRequirement selected).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    { unfold base, refined. reflexivity. }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericCostRequirement selected).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    { unfold base, refined. reflexivity. }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
  - pose (refined := Phase1GenericEnvironmentRequirement selected).
    assert (Hrefined :
      phase1_surface_normalize_generic_requirement_type_spine base =
        Some refined).
    { unfold base, refined. reflexivity. }
    assert (Hnormalize :
      phase1_surface_normalize_generic_requirement_type_tree tree =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirement_type_tree.
      rewrite Hbase.
      exact Hrefined.
    }
    exists refined.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
      exact Hnormalize.
Qed.
