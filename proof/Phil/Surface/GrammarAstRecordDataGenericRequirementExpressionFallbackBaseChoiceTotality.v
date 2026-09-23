From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceSpine
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceTotality
  GrammarAstRecordDataGenericRequirementExpressionOuterTotality
  GrammarAstRecordFieldsTotality
  GrammarAstDataTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the declaration-level fallback/base-choice refinement from #1341.

  The carrier introduced there advances only the optional generic-requirements
  field of record_decl and data_decl from the expression-outer carrier to the
  fallback/base-choice carrier. This file proves that refinement is total for
  derivable declaration trees while preserving exact parse-tree round trips.
*)

Lemma
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_total_from_spine_derivation :
  forall requirements path input rest,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_requirements"))
      input rest
      (phase1_surface_optional_generic_requirements_expression_outer_tree requirements) ->
    exists refined,
      phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice
        requirements = Some refined.
Proof.
  intros [requirements |] path input rest Hderive.
  - cbn in Hderive |- *.
    inversion Hderive; subst.
    match goal with
    | Hbody : Derives phase1_surface_rules _
        (ENonterminal "generic_requirements") _ _
        (phase1_surface_generic_requirements_expression_outer_spine_tree requirements)
        |- _ =>
        destruct
          (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine_total_from_spine_derivation
            requirements _ _ _ Hbody)
          as [refined Hrefined];
        exists (Some refined);
        cbn;
        rewrite Hrefined;
        reflexivity
    end.
  - cbn.
    exists None.
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree
        tree = Some refined /\
      phase1_surface_record_generic_requirement_expression_fallback_base_choice_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_record_generic_requirement_expression_outer_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  destruct base as [name generic_params mode requirements fields].
  cbn in Hbase, Hbase_round_trip.
  rewrite <- Hbase_round_trip in Hderive.
  unfold phase1_surface_record_generic_requirement_expression_outer_spine_tree in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "record_decl"
      input rest
      (PTNonterminal "record_decl"
        (PTSequence
          [ PTLiteral "record";
            phase1_surface_identifier_tree name;
            phase1_surface_optional_generic_params_kind_type_tree generic_params;
            phase1_surface_optional_mode_tree mode;
            phase1_surface_optional_generic_requirements_expression_outer_tree requirements;
            PTLiteral "{";
            phase1_surface_optional_field_type_list_tree fields;
            PTLiteral "}"
          ]))
      Hderive)
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
          (ESequence [ELiteral "mode"; ENonterminal "structural_mode"]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}"
      ]
      input rest
      (PTSequence
        [ PTLiteral "record";
          phase1_surface_identifier_tree name;
          phase1_surface_optional_generic_params_kind_type_tree generic_params;
          phase1_surface_optional_mode_tree mode;
          phase1_surface_optional_generic_requirements_expression_outer_tree requirements;
          PTLiteral "{";
          phase1_surface_optional_field_type_list_tree fields;
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
  | Hrequirements : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_requirements"))
      _ _
      (phase1_surface_optional_generic_requirements_expression_outer_tree requirements)
      |- _ =>
      destruct
        (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_total_from_spine_derivation
          requirements _ _ _ Hrequirements)
        as [refined_requirements Hrefined_requirements];
      let refined := constr:(
        {| phase1_record_generic_requirement_expression_fallback_base_choice_spine_name := name;
           phase1_record_generic_requirement_expression_fallback_base_choice_spine_generic_params :=
             generic_params;
           phase1_record_generic_requirement_expression_fallback_base_choice_spine_mode := mode;
           phase1_record_generic_requirement_expression_fallback_base_choice_spine_requirements :=
             refined_requirements;
           phase1_record_generic_requirement_expression_fallback_base_choice_spine_fields :=
             fields |}) in
      assert (Hnormalize :
        phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree
          tree = Some refined);
      [ unfold
          phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree;
        rewrite Hbase;
        unfold
          phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_spine;
        cbn;
        rewrite Hrefined_requirements;
        reflexivity
      | exists refined;
        split;
        [ exact Hnormalize
        | eapply
            phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Theorem
  phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree
        tree = Some refined /\
      phase1_surface_data_generic_requirement_expression_fallback_base_choice_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_data_generic_requirement_expression_outer_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  destruct base as
    [name generic_params mode requirements first_variant rest_variants].
  cbn in Hbase, Hbase_round_trip.
  rewrite <- Hbase_round_trip in Hderive.
  unfold phase1_surface_data_generic_requirement_expression_outer_spine_tree in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "data_decl"
      input rest
      (PTNonterminal "data_decl"
        (PTSequence
          [ PTLiteral "data";
            phase1_surface_identifier_tree name;
            phase1_surface_optional_generic_params_kind_type_tree generic_params;
            phase1_surface_optional_mode_tree mode;
            phase1_surface_optional_generic_requirements_expression_outer_tree requirements;
            PTLiteral "=";
            phase1_surface_record_field_type_variant_spine_tree first_variant;
            PTRepetition
              (map phase1_surface_record_field_type_data_suffix_tree
                rest_variants);
            PTLiteral ";"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_data_decl_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl"))
      [ ELiteral "data";
        ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence [ELiteral "mode"; ENonterminal "structural_mode"]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";"
      ]
      input rest
      (PTSequence
        [ PTLiteral "data";
          phase1_surface_identifier_tree name;
          phase1_surface_optional_generic_params_kind_type_tree generic_params;
          phase1_surface_optional_mode_tree mode;
          phase1_surface_optional_generic_requirements_expression_outer_tree requirements;
          PTLiteral "=";
          phase1_surface_record_field_type_variant_spine_tree first_variant;
          PTRepetition
            (map phase1_surface_record_field_type_data_suffix_tree rest_variants);
          PTLiteral ";"
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
  | Hrequirements : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_requirements"))
      _ _
      (phase1_surface_optional_generic_requirements_expression_outer_tree requirements)
      |- _ =>
      destruct
        (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_total_from_spine_derivation
          requirements _ _ _ Hrequirements)
        as [refined_requirements Hrefined_requirements];
      let refined := constr:(
        {| phase1_data_generic_requirement_expression_fallback_base_choice_spine_name := name;
           phase1_data_generic_requirement_expression_fallback_base_choice_spine_generic_params :=
             generic_params;
           phase1_data_generic_requirement_expression_fallback_base_choice_spine_mode := mode;
           phase1_data_generic_requirement_expression_fallback_base_choice_spine_requirements :=
             refined_requirements;
           phase1_data_generic_requirement_expression_fallback_base_choice_spine_first_variant :=
             first_variant;
           phase1_data_generic_requirement_expression_fallback_base_choice_spine_rest_variants :=
             rest_variants |}) in
      assert (Hnormalize :
        phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree
          tree = Some refined);
      [ unfold
          phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree;
        rewrite Hbase;
        unfold
          phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_spine;
        cbn;
        rewrite Hrefined_requirements;
        reflexivity
      | exists refined;
        split;
        [ exact Hnormalize
        | eapply
            phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
