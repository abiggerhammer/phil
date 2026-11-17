From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSourceHeader
  GrammarAstStructuralModeSpine
  GrammarAstRecordFieldTypeSpine
  GrammarAstGenericParamsSpine
  GrammarAstGenericRequirementsSpine
  GrammarAstRecordFieldsSpine
  GrammarAstRecordFieldsTotality
  GrammarAstOptionalFieldTypeTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the record-level field-type refinement from #1172. *)

Theorem phase1_surface_normalize_record_field_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_field_type_tree tree = Some refined /\
      phase1_surface_record_field_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_record_fields_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hbase as Hbase_layers.
  unfold phase1_surface_normalize_record_fields_tree in Hbase_layers.
  destruct (phase1_surface_normalize_record_requirements_tree tree)
    as [requirements |] eqn:Hrequirements;
    try discriminate Hbase_layers.
  pose proof
    (phase1_surface_normalize_record_requirements_tree_round_trip
      tree requirements Hrequirements)
    as Hrequirements_round_trip.
  destruct requirements as
    [name generic_params mode generic_requirements fields_tree].
  cbn in Hbase_layers, Hrequirements_round_trip.
  unfold phase1_surface_normalize_record_fields_spine in Hbase_layers.
  cbn in Hbase_layers.
  destruct (phase1_surface_normalize_optional_fields fields_tree)
    as [fields |] eqn:Hfields;
    try discriminate Hbase_layers.
  inversion Hbase_layers; subst base.
  clear Hbase_layers.

  pose proof Hderive as Hcanonical.
  rewrite <- Hrequirements_round_trip in Hcanonical.
  unfold phase1_surface_record_requirements_spine_tree in Hcanonical.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "record_decl"
      input rest
      (PTNonterminal "record_decl"
        (PTSequence
          [ PTLiteral "record";
            phase1_surface_identifier_tree name;
            phase1_surface_optional_generic_params_tree generic_params;
            phase1_surface_optional_mode_tree mode;
            phase1_surface_optional_generic_requirements_tree
              generic_requirements;
            PTLiteral "{";
            fields_tree;
            PTLiteral "}"
          ]))
      Hcanonical)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_record_decl_fields_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
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
      input rest
      (PTSequence
        [ PTLiteral "record";
          phase1_surface_identifier_tree name;
          phase1_surface_optional_generic_params_tree generic_params;
          phase1_surface_optional_mode_tree mode;
          phase1_surface_optional_generic_requirements_tree generic_requirements;
          PTLiteral "{";
          fields_tree;
          PTLiteral "}"
        ])
      Hbody)
    as [trees [Hsequence_tree Hitems]].
  (* Peel off the grammar sequence with the exact indexed transport
     lemmas, retaining the seventh child's canonical Derives witness. *)
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 0
      (ELiteral "record")
      [ ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence
            [ ELiteral "mode"; ENonterminal "structural_mode" ]);
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
            [ ELiteral "mode"; ENonterminal "structural_mode" ]);
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
            [ ELiteral "mode"; ENonterminal "structural_mode" ]);
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
          [ ELiteral "mode"; ENonterminal "structural_mode" ]))
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
      [Htail4_trees [Hrequirements_derive Htail5]]]]].
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
    as [after_fields [derived_fields_tree [tail7_trees
      [Htail6_trees [Hfields_derive Htail7]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees,
    Htail4_trees, Htail5_trees, Htail6_trees in Hsequence_tree.
  inversion Hsequence_tree; subst derived_fields_tree.
  destruct
    (phase1_surface_normalize_optional_field_type_tree_total_from_derivation
      _ _ _ fields_tree Hfields_derive)
    as [base_fields [refined_fields
        [Hbase_fields [Hrefined_fields Hrefined_fields_tree]]]].
  rewrite Hfields in Hbase_fields.
  inversion Hbase_fields; subst base_fields.
  let refined := constr:(
    {| phase1_record_field_type_spine_name := name;
       phase1_record_field_type_spine_generic_params := generic_params;
       phase1_record_field_type_spine_mode := mode;
       phase1_record_field_type_spine_requirements := generic_requirements;
       phase1_record_field_type_spine_fields := refined_fields |}) in
  assert (Hrefined :
    phase1_surface_normalize_record_field_type_spine
      {| phase1_record_fields_spine_name := name;
         phase1_record_fields_spine_generic_params := generic_params;
         phase1_record_fields_spine_mode := mode;
         phase1_record_fields_spine_requirements := generic_requirements;
         phase1_record_fields_spine_fields := fields |}
      = Some refined);
  [ unfold phase1_surface_normalize_record_field_type_spine;
    cbn;
    rewrite Hrefined_fields;
    reflexivity
  | assert (Hnormalize :
      phase1_surface_normalize_record_field_type_tree tree = Some refined);
    [ unfold phase1_surface_normalize_record_field_type_tree;
      rewrite Hbase;
      exact Hrefined
    | exists refined;
      split;
      [ exact Hnormalize
      | eapply phase1_surface_normalize_record_field_type_tree_round_trip;
        exact Hnormalize ] ] ].
Qed.
