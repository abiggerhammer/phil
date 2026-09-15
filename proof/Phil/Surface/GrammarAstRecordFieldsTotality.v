From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSourceHeaderTotality
  GrammarAstGenericParamsTotality
  GrammarAstStructuralModeTotality
  GrammarAstRecordFieldsSpine
  GrammarAstGenericRequirementsSpine
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the record-field correspondence introduced by #949. *)

Definition phase1_surface_field_suffix_expression_for_totality : EbnfExpression :=
  ESequence
    [ ELiteral ",";
      ENonterminal "field_decl"
    ].

Definition phase1_surface_field_list_expression_for_totality : EbnfExpression :=
  ESequence
    [ ENonterminal "field_decl";
      ERepetition phase1_surface_field_suffix_expression_for_totality;
      EOptional (ELiteral ",")
    ].

Definition phase1_surface_optional_fields_expression_for_totality : EbnfExpression :=
  EOptional phase1_surface_field_list_expression_for_totality.

Lemma phase1_surface_field_decl_lookup_for_totality :
  lookupRule "field_decl" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "type_expression"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_record_decl_fields_lookup_for_totality :
  lookupRule "record_decl" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "record";
          ENonterminal "identifier";
          EOptional (ENonterminal "generic_params");
          EOptional
            (ESequence
              [ ELiteral "mode";
                ENonterminal "structural_mode"
              ]);
          EOptional (ENonterminal "generic_requirements");
          ELiteral "{";
          phase1_surface_optional_fields_expression_for_totality;
          ELiteral "}"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_field_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "field_decl")
      input rest tree ->
    exists field,
      phase1_surface_normalize_field_spine tree = Some field /\
      phase1_surface_field_spine_tree field = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "field_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_field_decl_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "field_decl"))
      [ ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "field_decl")) 0
      (ENonterminal "identifier")
      [ ELiteral ":";
        ENonterminal "type_expression" ]
      input rest trees Hitems)
    as [after_name [name_tree [tail1_trees
      [Htrees [Hname Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "field_decl")) 1
      (ELiteral ":")
      [ ENonterminal "type_expression" ]
      after_name rest tail1_trees Htail1)
    as [after_colon [colon_tree [tail2_trees
      [Htail1_trees [Hcolon Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "field_decl")) 2
      (ENonterminal "type_expression") []
      after_colon rest tail2_trees Htail2)
    as [after_type [type_tree [nil_trees
      [Htail2_trees [Htype Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
    as [colon_tail [_ [_ Hcolon_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "type_expression" _ _ _ type_tree Htype) as Htype_validate.
  pose (field :=
    {| phase1_field_spine_name := name;
       phase1_field_spine_type_tree := type_tree |}).
  assert (Hnormalize :
    phase1_surface_normalize_field_spine tree = Some field).
  {
    rewrite Htree, Hsubtree, Hcolon_tree.
    unfold phase1_surface_normalize_field_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hname_normalize.
    rewrite Htype_validate.
    unfold field.
    reflexivity.
  }
  exists field.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_field_spine_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_field_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_field_suffix_expression_for_totality
      input rest tree ->
    exists field,
      phase1_surface_normalize_field_suffix tree = Some field /\
      phase1_surface_field_suffix_tree field = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_field_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral ",";
        ENonterminal "field_decl"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral ",")
      [ ENonterminal "field_decl" ]
      input rest trees Hitems)
    as [after_comma [comma_tree [tail1_trees
      [Htrees [Hcomma Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "field_decl") []
      after_comma rest tail1_trees Htail1)
    as [after_field [field_tree [nil_trees
      [Htail1_trees [Hfield Hnil]]]]].
  rewrite Htrees, Htail1_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "," _ _ comma_tree Hcomma)
    as [comma_tail [_ [_ Hcomma_tree]]].
  destruct
    (phase1_surface_normalize_field_spine_total_from_derivation
      _ _ _ field_tree Hfield)
    as [field [Hfield_normalize Hfield_round_trip]].
  assert (Hnormalize :
    phase1_surface_normalize_field_suffix tree = Some field).
  {
    rewrite Htree, Hcomma_tree.
    unfold phase1_surface_normalize_field_suffix,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hfield_normalize.
    reflexivity.
  }
  exists field.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_field_suffix_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_field_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_field_suffix_expression_for_totality ->
    exists fields,
      phase1_surface_normalize_field_suffixes trees = Some fields.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [].
    reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_field_suffix_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [field [Htree Htree_round_trip]].
    destruct (IHrest eq_refl) as [fields Hfields].
    exists (field :: fields).
    cbn.
    rewrite Htree.
    rewrite Hfields.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_trailing_comma_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (EOptional (ELiteral ","))
      input rest tree ->
    exists present,
      phase1_surface_normalize_trailing_comma tree = Some present /\
      phase1_surface_trailing_comma_tree present = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ELiteral ",")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_trailing_comma tree = Some false).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists false.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_trailing_comma_round_trip.
      exact Hnormalize.
  - destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "," _ _ body Hbody)
      as [tail [_ [_ Hcomma_tree]]].
    assert (Hnormalize :
      phase1_surface_normalize_trailing_comma tree = Some true).
    {
      rewrite Hsome.
      rewrite Hcomma_tree.
      reflexivity.
    }
    exists true.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_trailing_comma_round_trip.
      exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_field_list_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_field_list_expression_for_totality
      input rest tree ->
    exists fields,
      phase1_surface_normalize_field_list_spine tree = Some fields /\
      phase1_surface_field_list_spine_tree fields = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_field_list_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ENonterminal "field_decl";
        ERepetition phase1_surface_field_suffix_expression_for_totality;
        EOptional (ELiteral ",")
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ENonterminal "field_decl")
      [ ERepetition phase1_surface_field_suffix_expression_for_totality;
        EOptional (ELiteral ",") ]
      input rest trees Hitems)
    as [after_first [first_tree [tail1_trees
      [Htrees [Hfirst Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ERepetition phase1_surface_field_suffix_expression_for_totality)
      [ EOptional (ELiteral ",") ]
      after_first rest tail1_trees Htail1)
    as [after_rest [rest_tree [tail2_trees
      [Htail1_trees [Hrest Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (EOptional (ELiteral ",")) []
      after_rest rest tail2_trees Htail2)
    as [after_trailing [trailing_tree [nil_trees
      [Htail2_trees [Htrailing Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (phase1_surface_normalize_field_spine_total_from_derivation
      _ _ _ first_tree Hfirst)
    as [first [Hfirst_normalize Hfirst_round_trip]].
  destruct
    (phase1_surface_repetition_derivation_exposes
      _ phase1_surface_field_suffix_expression_for_totality
      _ _ rest_tree Hrest)
    as [rest_trees [Hrest_tree Hrest_body]].
  destruct
    (phase1_surface_normalize_field_suffixes_total_from_repetition
      _ phase1_surface_field_suffix_expression_for_totality
      _ _ rest_trees Hrest_body eq_refl)
    as [rest_fields Hrest_normalize].
  destruct
    (phase1_surface_normalize_trailing_comma_total_from_derivation
      _ _ _ trailing_tree Htrailing)
    as [trailing [Htrailing_normalize Htrailing_round_trip]].
  pose (fields :=
    {| phase1_field_list_spine_first := first;
       phase1_field_list_spine_rest := rest_fields;
       phase1_field_list_spine_trailing_comma := trailing |}).
  assert (Hnormalize :
    phase1_surface_normalize_field_list_spine tree = Some fields).
  {
    rewrite Htree, Hrest_tree.
    unfold phase1_surface_normalize_field_list_spine,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_repetition.
    cbn.
    rewrite Hfirst_normalize.
    rewrite Htrailing_normalize.
    rewrite Hrest_normalize.
    unfold fields.
    reflexivity.
  }
  exists fields.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_field_list_spine_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_optional_fields_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_optional_fields_expression_for_totality
      input rest tree ->
    exists fields,
      phase1_surface_normalize_optional_fields tree = Some fields /\
      phase1_surface_optional_fields_tree fields = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_optional_fields_expression_for_totality in Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      phase1_surface_field_list_expression_for_totality
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_fields tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_fields_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_field_list_spine_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [fields [Hfields Hfields_round_trip]].
    assert (Hnormalize :
      phase1_surface_normalize_optional_fields tree = Some (Some fields)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_fields,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hfields.
      reflexivity.
    }
    exists (Some fields).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_fields_round_trip.
      exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_record_fields_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_fields_tree tree = Some refined /\
      phase1_surface_record_fields_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "record_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_record_decl_fields_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl"))
      [ ELiteral "record";
        ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence
            [ ELiteral "mode";
              ENonterminal "structural_mode"
            ]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 0
      (ELiteral "record")
      [ ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence
            [ ELiteral "mode";
              ENonterminal "structural_mode" ]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}" ]
      input rest trees Hitems)
    as [after_keyword [keyword_tree [tail1_trees
      [Htrees [Hkeyword Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 1
      (ENonterminal "identifier")
      [ EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence
            [ ELiteral "mode";
              ENonterminal "structural_mode" ]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}" ]
      after_keyword rest tail1_trees Htail1)
    as [after_name [name_tree [tail2_trees
      [Htail1_trees [Hname Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 2
      (EOptional (ENonterminal "generic_params"))
      [ EOptional
          (ESequence
            [ ELiteral "mode";
              ENonterminal "structural_mode" ]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}" ]
      after_name rest tail2_trees Htail2)
    as [after_generic [generic_tree [tail3_trees
      [Htail2_trees [Hgeneric Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 3
      (EOptional
        (ESequence
          [ ELiteral "mode";
            ENonterminal "structural_mode" ]))
      [ EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}" ]
      after_generic rest tail3_trees Htail3)
    as [after_mode [mode_tree [tail4_trees
      [Htail3_trees [Hmode Htail4]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 4
      (EOptional (ENonterminal "generic_requirements"))
      [ ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}" ]
      after_mode rest tail4_trees Htail4)
    as [after_requirements [requirements_tree [tail5_trees
      [Htail4_trees [Hrequirements Htail5]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 5
      (ELiteral "{")
      [ phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}" ]
      after_requirements rest tail5_trees Htail5)
    as [after_open [open_tree [tail6_trees
      [Htail5_trees [Hopen Htail6]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 6
      phase1_surface_optional_fields_expression_for_totality
      [ ELiteral "}" ]
      after_open rest tail6_trees Htail6)
    as [after_fields [fields_tree [tail7_trees
      [Htail6_trees [Hfields Htail7]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 7
      (ELiteral "}") []
      after_fields rest tail7_trees Htail7)
    as [after_close [close_tree [nil_trees
      [Htail7_trees [Hclose Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees,
    Htail4_trees, Htail5_trees, Htail6_trees, Htail7_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "record" _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "{" _ _ open_tree Hopen)
    as [open_tail [_ [_ Hopen_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "}" _ _ close_tree Hclose)
    as [close_tail [_ [_ Hclose_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  destruct
    (phase1_surface_normalize_optional_generic_params_total_from_derivation
      _ _ _ generic_tree Hgeneric)
    as [parameters [Hgeneric_normalize Hgeneric_round_trip]].
  destruct
    (phase1_surface_normalize_optional_mode_total_from_derivation
      _ _ _ mode_tree Hmode)
    as [mode [Hmode_normalize Hmode_round_trip]].
  destruct
    (phase1_surface_normalize_optional_generic_requirements_total_from_derivation
      _ _ _ requirements_tree Hrequirements)
    as [requirements [Hrequirements_normalize Hrequirements_round_trip]].
  destruct
    (phase1_surface_normalize_optional_fields_total_from_derivation
      _ _ _ fields_tree Hfields)
    as [fields [Hfields_normalize Hfields_round_trip]].
  pose (record :=
    {| phase1_record_spine_name := name;
       phase1_record_spine_generic_params_tree := generic_tree;
       phase1_record_spine_mode_tree := mode_tree;
       phase1_record_spine_requirements_tree := requirements_tree;
       phase1_record_spine_fields_tree := fields_tree |}).
  assert (Hrecord_normalize :
    phase1_surface_normalize_record_spine tree = Some record).
  {
    rewrite Htree, Hsubtree, Hkeyword_tree, Hopen_tree, Hclose_tree.
    unfold phase1_surface_normalize_record_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact8,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hname_normalize.
    unfold record.
    reflexivity.
  }
  pose (generic_refined :=
    {| phase1_record_generic_spine_name := name;
       phase1_record_generic_spine_generic_params := parameters;
       phase1_record_generic_spine_mode_tree := mode_tree;
       phase1_record_generic_spine_requirements_tree := requirements_tree;
       phase1_record_generic_spine_fields_tree := fields_tree |}).
  assert (Hgeneric_tree_normalize :
    phase1_surface_normalize_record_generic_tree tree = Some generic_refined).
  {
    unfold phase1_surface_normalize_record_generic_tree.
    rewrite Hrecord_normalize.
    unfold phase1_surface_normalize_record_generic_spine.
    replace (phase1_record_spine_generic_params_tree record)
      with generic_tree.
    - rewrite Hgeneric_normalize.
      unfold record, generic_refined.
      reflexivity.
    - unfold record.
      reflexivity.
  }
  pose (mode_refined :=
    {| phase1_record_mode_spine_name := name;
       phase1_record_mode_spine_generic_params := parameters;
       phase1_record_mode_spine_mode := mode;
       phase1_record_mode_spine_requirements_tree := requirements_tree;
       phase1_record_mode_spine_fields_tree := fields_tree |}).
  assert (Hmode_tree_normalize :
    phase1_surface_normalize_record_mode_tree tree = Some mode_refined).
  {
    unfold phase1_surface_normalize_record_mode_tree.
    rewrite Hgeneric_tree_normalize.
    unfold phase1_surface_normalize_record_mode_spine.
    replace (phase1_record_generic_spine_mode_tree generic_refined)
      with mode_tree.
    - rewrite Hmode_normalize.
      unfold generic_refined, mode_refined.
      reflexivity.
    - unfold generic_refined.
      reflexivity.
  }
  pose (requirements_refined :=
    {| phase1_record_requirements_spine_name := name;
       phase1_record_requirements_spine_generic_params := parameters;
       phase1_record_requirements_spine_mode := mode;
       phase1_record_requirements_spine_requirements := requirements;
       phase1_record_requirements_spine_fields_tree := fields_tree |}).
  assert (Hrequirements_tree_normalize :
    phase1_surface_normalize_record_requirements_tree tree =
      Some requirements_refined).
  {
    unfold phase1_surface_normalize_record_requirements_tree.
    rewrite Hmode_tree_normalize.
    unfold phase1_surface_normalize_record_requirements_spine.
    replace (phase1_record_mode_spine_requirements_tree mode_refined)
      with requirements_tree.
    - rewrite Hrequirements_normalize.
      unfold mode_refined, requirements_refined.
      reflexivity.
    - unfold mode_refined.
      reflexivity.
  }
  pose (refined :=
    {| phase1_record_fields_spine_name := name;
       phase1_record_fields_spine_generic_params := parameters;
       phase1_record_fields_spine_mode := mode;
       phase1_record_fields_spine_requirements := requirements;
       phase1_record_fields_spine_fields := fields |}).
  assert (Hnormalize :
    phase1_surface_normalize_record_fields_tree tree = Some refined).
  {
    unfold phase1_surface_normalize_record_fields_tree.
    rewrite Hrequirements_tree_normalize.
    unfold phase1_surface_normalize_record_fields_spine.
    replace (phase1_record_requirements_spine_fields_tree requirements_refined)
      with fields_tree.
    - rewrite Hfields_normalize.
      unfold requirements_refined, refined.
      reflexivity.
    - unfold requirements_refined.
      reflexivity.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_record_fields_tree_round_trip.
    exact Hnormalize.
Qed.
