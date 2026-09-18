From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordFieldTypeSpine
  GrammarAstRecordFieldsTotality
  GrammarAstOptionalFieldTypeTotality.

Import ListNotations.

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
  inversion Hsequence_tree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hfields_derive : Derives phase1_surface_rules _
      phase1_surface_optional_fields_expression_for_totality
      _ _ fields_tree |- _ =>
      destruct
        (phase1_surface_normalize_optional_field_type_tree_total_from_derivation
          _ _ _ fields_tree Hfields_derive)
        as [base_fields [refined_fields
            [Hbase_fields [Hrefined_fields Hrefined_fields_tree]]]];
      rewrite Hfields in Hbase_fields;
      inversion Hbase_fields; subst base_fields;
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
            exact Hnormalize ] ] ]
  end.
Qed.
