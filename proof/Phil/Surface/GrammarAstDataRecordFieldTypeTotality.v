From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstDataRecordFieldTypeSpine
  GrammarAstVariantDeclRecordFieldTypeTotality
  GrammarAstDataTotality.

Import ListNotations.

(* Converse for the data-level record-field-type refinement from #1184. *)

Lemma phase1_surface_normalize_record_field_type_variant_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "variant_decl")
      input rest tree ->
    exists base middle refined,
      phase1_surface_normalize_variant_spine tree = Some base /\
      phase1_surface_normalize_variant_payload_variant_spine base = Some middle /\
      phase1_surface_normalize_record_field_type_variant_spine middle =
        Some refined /\
      phase1_surface_record_field_type_variant_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_variant_layers_total_from_derivation
      path input rest tree Hderive)
    as [base [middle [Hbase [Hmiddle Hmiddle_tree]]]].
  destruct
    (phase1_surface_normalize_record_field_type_variant_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hrefined_tree Hrefined_round_trip]].
  assert (Hrefined :
    phase1_surface_normalize_record_field_type_variant_spine middle =
      Some refined).
  {
    unfold phase1_surface_normalize_record_field_type_variant_tree
      in Hrefined_tree.
    rewrite Hbase, Hmiddle in Hrefined_tree.
    exact Hrefined_tree.
  }
  exists base, middle, refined.
  repeat split; assumption.
Qed.

Lemma
  phase1_surface_normalize_record_field_type_data_variant_suffix_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_data_variant_suffix_expression_for_totality
      input rest tree ->
    exists raw_variant base_variant middle_variant refined_variant,
      phase1_surface_normalize_data_variant_suffix tree = Some raw_variant /\
      phase1_surface_normalize_variant_spine raw_variant = Some base_variant /\
      phase1_surface_normalize_variant_payload_variant_spine base_variant =
        Some middle_variant /\
      phase1_surface_normalize_record_field_type_variant_spine middle_variant =
        Some refined_variant.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_data_variant_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "|";
        ENonterminal "variant_decl"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral "|")
      [ ENonterminal "variant_decl" ]
      input rest trees Hitems)
    as [after_bar [bar_tree [tail1_trees
      [Htrees [Hbar Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "variant_decl") []
      after_bar rest tail1_trees Htail1)
    as [after_variant [variant_tree [nil_trees
      [Htail1_trees [Hvariant Hnil]]]]].
  rewrite Htrees, Htail1_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "|" _ _ bar_tree Hbar)
    as [bar_tail [_ [_ Hbar_tree]]].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "variant_decl" _ _ _ variant_tree Hvariant) as Hvariant_validate.
  destruct
    (phase1_surface_normalize_record_field_type_variant_layers_total_from_derivation
      _ _ _ variant_tree Hvariant)
    as [base [middle [refined
      [Hbase [Hmiddle [Hrefined Hround_trip]]]]]].
  assert (Hraw :
    phase1_surface_normalize_data_variant_suffix tree = Some variant_tree).
  {
    rewrite Htree, Hbar_tree.
    unfold phase1_surface_normalize_data_variant_suffix,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hvariant_validate.
    reflexivity.
  }
  exists variant_tree, base, middle, refined.
  repeat split; assumption.
Qed.

Lemma
  phase1_surface_normalize_record_field_type_data_variant_layers_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_data_variant_suffix_expression_for_totality ->
    exists raw_variants base_variants middle_variants refined_variants,
      phase1_surface_normalize_data_variant_suffixes trees = Some raw_variants /\
      phase1_surface_normalize_variant_spines raw_variants = Some base_variants /\
      phase1_surface_normalize_variant_payload_variant_spines base_variants =
        Some middle_variants /\
      phase1_surface_normalize_record_field_type_variant_spines middle_variants =
        Some refined_variants.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [], [], [], [].
    repeat split; reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_record_field_type_data_variant_suffix_layers_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [raw [base [middle_variant [refined
        [Hraw [Hbase [Hmiddle Hrefined]]]]]]].
    destruct (IHrest eq_refl)
      as [raws [bases [middles [refineds
        [Hraws [Hbases [Hmiddles Hrefineds]]]]]]].
    exists (raw :: raws), (base :: bases),
      (middle_variant :: middles), (refined :: refineds).
    repeat split.
    + cbn. rewrite Hraw, Hraws. reflexivity.
    + cbn. rewrite Hbase, Hbases. reflexivity.
    + cbn. rewrite Hmiddle, Hmiddles. reflexivity.
    + cbn. rewrite Hrefined, Hrefineds. reflexivity.
Qed.

Theorem phase1_surface_normalize_data_record_field_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_data_record_field_type_tree tree =
        Some refined /\
      phase1_surface_data_record_field_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "data_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_data_decl_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl"))
      [ ELiteral "data";
        ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence
            [ ELiteral "mode";
              ENonterminal "structural_mode"
            ]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 0
      (ELiteral "data")
      [ ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence [ELiteral "mode"; ENonterminal "structural_mode"]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";" ]
      input rest trees Hitems)
    as [after_keyword [keyword_tree [tail1_trees
      [Htrees [Hkeyword Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 1
      (ENonterminal "identifier")
      [ EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence [ELiteral "mode"; ENonterminal "structural_mode"]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";" ]
      after_keyword rest tail1_trees Htail1)
    as [after_name [name_tree [tail2_trees
      [Htail1_trees [Hname Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 2
      (EOptional (ENonterminal "generic_params"))
      [ EOptional
          (ESequence [ELiteral "mode"; ENonterminal "structural_mode"]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";" ]
      after_name rest tail2_trees Htail2)
    as [after_generic [generic_tree [tail3_trees
      [Htail2_trees [Hgeneric Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 3
      (EOptional
        (ESequence [ELiteral "mode"; ENonterminal "structural_mode"]))
      [ EOptional (ENonterminal "generic_requirements");
        ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";" ]
      after_generic rest tail3_trees Htail3)
    as [after_mode [mode_tree [tail4_trees
      [Htail3_trees [Hmode Htail4]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 4
      (EOptional (ENonterminal "generic_requirements"))
      [ ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";" ]
      after_mode rest tail4_trees Htail4)
    as [after_requirements [requirements_tree [tail5_trees
      [Htail4_trees [Hrequirements Htail5]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 5
      (ELiteral "=")
      [ ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";" ]
      after_requirements rest tail5_trees Htail5)
    as [after_equals [equals_tree [tail6_trees
      [Htail5_trees [Hequals Htail6]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 6
      (ENonterminal "variant_decl")
      [ ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";" ]
      after_equals rest tail6_trees Htail6)
    as [after_first [first_tree [tail7_trees
      [Htail6_trees [Hfirst Htail7]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 7
      (ERepetition phase1_surface_data_variant_suffix_expression_for_totality)
      [ ELiteral ";" ]
      after_first rest tail7_trees Htail7)
    as [after_rest [rest_tree [tail8_trees
      [Htail7_trees [Hrest Htail8]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl")) 8
      (ELiteral ";") []
      after_rest rest tail8_trees Htail8)
    as [after_terminator [terminator_tree [nil_trees
      [Htail8_trees [Hterminator Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees,
    Htail4_trees, Htail5_trees, Htail6_trees, Htail7_trees,
    Htail8_trees in Hsubtree.
  inversion Hnil; subst nil_trees.

  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "data" _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "=" _ _ equals_tree Hequals)
    as [equals_tail [_ [_ Hequals_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
    as [terminator_tail [_ [_ Hterminator_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  destruct
    (phase1_surface_normalize_optional_generic_params_total_from_derivation
      _ _ _ generic_tree Hgeneric)
    as [generic_params [Hgeneric_normalize Hgeneric_round_trip]].
  destruct
    (phase1_surface_normalize_optional_mode_total_from_derivation
      _ _ _ mode_tree Hmode)
    as [mode [Hmode_normalize Hmode_round_trip]].
  destruct
    (phase1_surface_normalize_optional_generic_requirements_total_from_derivation
      _ _ _ requirements_tree Hrequirements)
    as [requirements [Hrequirements_normalize Hrequirements_round_trip]].

  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "variant_decl" _ _ _ first_tree Hfirst) as Hfirst_validate.
  destruct
    (phase1_surface_normalize_record_field_type_variant_layers_total_from_derivation
      _ _ _ first_tree Hfirst)
    as [first_base [first_middle [first_refined
      [Hfirst_base [Hfirst_middle [Hfirst_refined Hfirst_round_trip]]]]]].

  destruct
    (phase1_surface_repetition_derivation_exposes
      _ phase1_surface_data_variant_suffix_expression_for_totality
      _ _ rest_tree Hrest)
    as [rest_trees [Hrest_tree Hrest_body]].
  destruct
    (phase1_surface_normalize_record_field_type_data_variant_layers_total_from_repetition
      _ phase1_surface_data_variant_suffix_expression_for_totality
      _ _ rest_trees Hrest_body eq_refl)
    as [raw_rest [base_rest [middle_rest [refined_rest
      [Hraw_rest [Hbase_rest [Hmiddle_rest Hrefined_rest]]]]]]].

  pose (raw_data :=
    {| phase1_data_spine_name := name;
       phase1_data_spine_generic_params := generic_params;
       phase1_data_spine_mode := mode;
       phase1_data_spine_requirements := requirements;
       phase1_data_spine_first_variant_tree := first_tree;
       phase1_data_spine_rest_variant_trees := raw_rest |}).
  pose (base_data :=
    {| phase1_data_variant_spine_name := name;
       phase1_data_variant_spine_generic_params := generic_params;
       phase1_data_variant_spine_mode := mode;
       phase1_data_variant_spine_requirements := requirements;
       phase1_data_variant_spine_first_variant := first_base;
       phase1_data_variant_spine_rest_variants := base_rest |}).
  pose (middle_data :=
    {| phase1_data_variant_payload_spine_name := name;
       phase1_data_variant_payload_spine_generic_params := generic_params;
       phase1_data_variant_payload_spine_mode := mode;
       phase1_data_variant_payload_spine_requirements := requirements;
       phase1_data_variant_payload_spine_first_variant := first_middle;
       phase1_data_variant_payload_spine_rest_variants := middle_rest |}).
  pose (refined_data :=
    {| phase1_data_record_field_type_spine_name := name;
       phase1_data_record_field_type_spine_generic_params := generic_params;
       phase1_data_record_field_type_spine_mode := mode;
       phase1_data_record_field_type_spine_requirements := requirements;
       phase1_data_record_field_type_spine_first_variant := first_refined;
       phase1_data_record_field_type_spine_rest_variants := refined_rest |}).

  assert (Hraw_data :
    phase1_surface_normalize_data_spine tree = Some raw_data).
  {
    rewrite Htree, Hsubtree, Hkeyword_tree,
      Hequals_tree, Hrest_tree, Hterminator_tree.
    unfold phase1_surface_normalize_data_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact9,
      phase1_surface_expect_literal,
      phase1_surface_expect_repetition.
    cbn.
    rewrite Hfirst_validate.
    rewrite Hname_normalize.
    rewrite Hgeneric_normalize.
    rewrite Hmode_normalize.
    rewrite Hrequirements_normalize.
    rewrite Hraw_rest.
    unfold raw_data.
    reflexivity.
  }
  assert (Hbase_data :
    phase1_surface_normalize_data_variant_spine raw_data = Some base_data).
  {
    unfold phase1_surface_normalize_data_variant_spine.
    unfold raw_data.
    cbn.
    rewrite Hfirst_base.
    rewrite Hbase_rest.
    unfold base_data.
    reflexivity.
  }
  assert (Hmiddle_data :
    phase1_surface_normalize_data_variant_payload_spine base_data =
      Some middle_data).
  {
    unfold phase1_surface_normalize_data_variant_payload_spine.
    unfold base_data.
    cbn.
    rewrite Hfirst_middle.
    rewrite Hmiddle_rest.
    unfold middle_data.
    reflexivity.
  }
  assert (Hrefined_data :
    phase1_surface_normalize_data_record_field_type_spine middle_data =
      Some refined_data).
  {
    unfold phase1_surface_normalize_data_record_field_type_spine.
    unfold middle_data.
    cbn.
    rewrite Hfirst_refined.
    rewrite Hrefined_rest.
    unfold refined_data.
    reflexivity.
  }

  assert (Hbase_tree :
    phase1_surface_normalize_data_variant_tree tree = Some base_data).
  {
    unfold phase1_surface_normalize_data_variant_tree.
    rewrite Hraw_data.
    exact Hbase_data.
  }
  assert (Hmiddle_tree :
    phase1_surface_normalize_data_variant_payload_tree tree = Some middle_data).
  {
    unfold phase1_surface_normalize_data_variant_payload_tree.
    rewrite Hbase_tree.
    exact Hmiddle_data.
  }
  assert (Hnormalize :
    phase1_surface_normalize_data_record_field_type_tree tree =
      Some refined_data).
  {
    unfold phase1_surface_normalize_data_record_field_type_tree.
    rewrite Hmiddle_tree.
    exact Hrefined_data.
  }

  exists refined_data.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_data_record_field_type_tree_round_trip.
    exact Hnormalize.
Qed.
