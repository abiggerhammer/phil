From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericKindTypeSpine
  GrammarAstGenericKindTypeTotality
  GrammarAstGenericParamKindTypeTotality
  GrammarAstRecordFieldTypeTotality
  GrammarAstDataRecordFieldTypeTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the declaration-level generic-kind type refinement from #1198. *)

Lemma phase1_surface_generic_kind_item_at_tag :
  forall tag,
    nth_error phase1_surface_generic_kind_items_for_totality
      (phase1_surface_generic_kind_tag_index tag) =
    Some (phase1_surface_generic_kind_expression_for_totality tag).
Proof.
  intros tag.
  destruct tag; reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_kind_type_spine_total_from_spine_derivation :
  forall kind path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_kind")
      input rest (phase1_surface_generic_kind_spine_tree kind) ->
    exists refined,
      phase1_surface_normalize_generic_kind_type_spine kind = Some refined.
Proof.
  intros [tag selected] path input rest Hderive.
  unfold phase1_surface_generic_kind_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_kind"
      input rest
      (PTNonterminal "generic_kind"
        (PTAlternative
          (phase1_surface_generic_kind_tag_index tag)
          selected))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_kind_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "generic_kind"))
      phase1_surface_generic_kind_items_for_totality
      input rest
      (PTAlternative
        (phase1_surface_generic_kind_tag_index tag)
        selected)
      Hbody)
    as [index [item [branch [Hnth [Hbranch Hselected]]]]].
  inversion Hbranch; subst index branch.
  rewrite phase1_surface_generic_kind_item_at_tag in Hnth.
  inversion Hnth; subst item.
  destruct tag; cbn in Hselected |- *.
  - exists Phase1GenericTypeKind.
    reflexivity.
  - exists Phase1GenericNatKind.
    reflexivity.
  - exists Phase1GenericSessionKind.
    reflexivity.
  - exists Phase1GenericMessageKind.
    reflexivity.
  - exists Phase1GenericEffectsKind.
    reflexivity.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type_total_from_derivation
        "provider" _ _ _ selected Hselected)
      as [type_value [Htype Hround_trip]].
    exists (Phase1GenericProviderKind type_value).
    rewrite Htype.
    reflexivity.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type_total_from_derivation
        "callable" _ _ _ selected Hselected)
      as [type_value [Htype Hround_trip]].
    exists (Phase1GenericCallableKind type_value).
    rewrite Htype.
    reflexivity.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type_total_from_derivation
        "boundary" _ _ _ selected Hselected)
      as [type_value [Htype Hround_trip]].
    exists (Phase1GenericBoundaryKind type_value).
    rewrite Htype.
    reflexivity.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type_total_from_derivation
        "architecture" _ _ _ selected Hselected)
      as [type_value [Htype Hround_trip]].
    exists (Phase1GenericArchitectureKind type_value).
    rewrite Htype.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_param_kind_type_spine_total_from_spine_derivation :
  forall parameter path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_param")
      input rest (phase1_surface_generic_param_spine_tree parameter) ->
    exists refined,
      phase1_surface_normalize_generic_param_kind_type_spine parameter =
        Some refined.
Proof.
  intros [name kind] path input rest Hderive.
  unfold phase1_surface_generic_param_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_param"
      input rest
      (PTNonterminal "generic_param"
        (PTSequence
          [ phase1_surface_identifier_tree name;
            PTLiteral ":";
            phase1_surface_generic_kind_spine_tree kind
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_param_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "generic_param"))
      [ ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "generic_kind"
      ]
      input rest
      (PTSequence
        [ phase1_surface_identifier_tree name;
          PTLiteral ":";
          phase1_surface_generic_kind_spine_tree kind
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
  | Hkind : Derives phase1_surface_rules _ (ENonterminal "generic_kind")
      _ _ (phase1_surface_generic_kind_spine_tree kind) |- _ =>
      destruct
        (phase1_surface_normalize_generic_kind_type_spine_total_from_spine_derivation
          kind _ _ _ Hkind)
        as [refined_kind Hrefined_kind];
      exists
        {| phase1_generic_param_kind_type_spine_name := name;
           phase1_generic_param_kind_type_spine_kind := refined_kind |};
      cbn;
      rewrite Hrefined_kind;
      reflexivity
  end.
Qed.

Lemma
  phase1_surface_normalize_generic_param_kind_type_suffix_total_from_spine_derivation :
  forall parameter path input rest,
    Derives phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "generic_param"])
      input rest (phase1_surface_generic_param_suffix_tree parameter) ->
    exists refined,
      phase1_surface_normalize_generic_param_kind_type_spine parameter =
        Some refined.
Proof.
  intros parameter path input rest Hderive.
  unfold phase1_surface_generic_param_suffix_tree in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral ",";
        ENonterminal "generic_param"
      ]
      input rest
      (PTSequence
        [ PTLiteral ",";
          phase1_surface_generic_param_spine_tree parameter
        ])
      Hderive)
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
  | Hparameter : Derives phase1_surface_rules _ (ENonterminal "generic_param")
      _ _ (phase1_surface_generic_param_spine_tree parameter) |- _ =>
      eapply
        phase1_surface_normalize_generic_param_kind_type_spine_total_from_spine_derivation;
      exact Hparameter
  end.
Qed.

Lemma
  phase1_surface_normalize_generic_param_kind_type_values_total_from_spine_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral ","; ENonterminal "generic_param"] ->
    forall parameters,
      trees = map phase1_surface_generic_param_suffix_tree parameters ->
      exists refined,
        phase1_surface_normalize_generic_param_kind_type_values parameters =
          Some refined.
Proof.
  intros path body input rest trees Hderive Hbody_shape.
  subst body.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros parameters Htrees.
  - destruct parameters as [|parameter parameters]; cbn in Htrees.
    + exists [].
      reflexivity.
    + discriminate Htrees.
  - destruct parameters as [|parameter parameters]; cbn in Htrees;
      try discriminate Htrees.
    inversion Htrees; subst tree trees.
    destruct
      (phase1_surface_normalize_generic_param_kind_type_suffix_total_from_spine_derivation
        parameter
        (descend path AtRepetitionBody)
        input middle Hitem)
      as [refined Hrefined].
    destruct (IHrest parameters eq_refl)
      as [refined_rest Hrefined_rest].
    exists (refined :: refined_rest).
    cbn.
    rewrite Hrefined, Hrefined_rest.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_params_kind_type_spine_total_from_spine_derivation :
  forall parameters path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_params")
      input rest (phase1_surface_generic_params_spine_tree parameters) ->
    exists refined,
      phase1_surface_normalize_generic_params_kind_type_spine parameters =
        Some refined.
Proof.
  intros [first rest_parameters] path input rest Hderive.
  unfold phase1_surface_generic_params_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_params"
      input rest
      (PTNonterminal "generic_params"
        (PTSequence
          [ PTLiteral "[";
            phase1_surface_generic_param_spine_tree first;
            PTRepetition
              (map phase1_surface_generic_param_suffix_tree rest_parameters);
            PTLiteral "]"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_params_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "generic_params"))
      [ ELiteral "[";
        ENonterminal "generic_param";
        ERepetition
          (ESequence [ELiteral ","; ENonterminal "generic_param"]);
        ELiteral "]"
      ]
      input rest
      (PTSequence
        [ PTLiteral "[";
          phase1_surface_generic_param_spine_tree first;
          PTRepetition
            (map phase1_surface_generic_param_suffix_tree rest_parameters);
          PTLiteral "]"
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
  | Hfirst : Derives phase1_surface_rules _ (ENonterminal "generic_param")
      _ _ (phase1_surface_generic_param_spine_tree first),
    Hrepeat : Derives phase1_surface_rules _
      (ERepetition
        (ESequence [ELiteral ","; ENonterminal "generic_param"]))
      _ _
      (PTRepetition
        (map phase1_surface_generic_param_suffix_tree rest_parameters)) |- _ =>
      destruct
        (phase1_surface_normalize_generic_param_kind_type_spine_total_from_spine_derivation
          first _ _ _ Hfirst)
        as [refined_first Hrefined_first];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _
          (ESequence [ELiteral ","; ENonterminal "generic_param"])
          _ _
          (PTRepetition
            (map phase1_surface_generic_param_suffix_tree rest_parameters))
          Hrepeat)
        as [rest_trees [Hrest_tree Hrest_body]];
      inversion Hrest_tree; subst rest_trees;
      destruct
        (phase1_surface_normalize_generic_param_kind_type_values_total_from_spine_repetition
          _
          (ESequence [ELiteral ","; ENonterminal "generic_param"])
          _ _
          (map phase1_surface_generic_param_suffix_tree rest_parameters)
          Hrest_body eq_refl
          rest_parameters eq_refl)
        as [refined_rest Hrefined_rest];
      exists
        {| phase1_generic_params_kind_type_spine_first := refined_first;
           phase1_generic_params_kind_type_spine_rest := refined_rest |};
      cbn;
      rewrite Hrefined_first, Hrefined_rest;
      reflexivity
  end.
Qed.

Lemma
  phase1_surface_normalize_optional_generic_params_kind_type_total_from_spine_derivation :
  forall parameters path input rest,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_params"))
      input rest (phase1_surface_optional_generic_params_tree parameters) ->
    exists refined,
      phase1_surface_normalize_optional_generic_params_kind_type parameters =
        Some refined.
Proof.
  intros [parameters |] path input rest Hderive.
  - cbn in Hderive |- *.
    inversion Hderive; subst.
    match goal with
    | Hbody : Derives phase1_surface_rules _
        (ENonterminal "generic_params") _ _
        (phase1_surface_generic_params_spine_tree parameters) |- _ =>
        destruct
          (phase1_surface_normalize_generic_params_kind_type_spine_total_from_spine_derivation
            parameters _ _ _ Hbody)
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
  phase1_surface_normalize_record_generic_kind_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_generic_kind_type_tree tree =
        Some refined /\
      phase1_surface_record_generic_kind_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_record_field_type_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  destruct base as [name generic_params mode requirements fields].
  cbn in Hbase, Hbase_round_trip.
  rewrite <- Hbase_round_trip in Hderive.
  unfold phase1_surface_record_field_type_spine_tree in Hderive.
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
            phase1_surface_optional_generic_requirements_tree requirements;
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
          phase1_surface_optional_generic_params_tree generic_params;
          phase1_surface_optional_mode_tree mode;
          phase1_surface_optional_generic_requirements_tree requirements;
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
  | Hgeneric : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_params"))
      _ _ (phase1_surface_optional_generic_params_tree generic_params) |- _ =>
      destruct
        (phase1_surface_normalize_optional_generic_params_kind_type_total_from_spine_derivation
          generic_params _ _ _ Hgeneric)
        as [refined_generic Hrefined_generic];
      let refined := constr:(
        {| phase1_record_generic_kind_type_spine_name := name;
           phase1_record_generic_kind_type_spine_generic_params :=
             refined_generic;
           phase1_record_generic_kind_type_spine_mode := mode;
           phase1_record_generic_kind_type_spine_requirements := requirements;
           phase1_record_generic_kind_type_spine_fields := fields |}) in
      assert (Hnormalize :
        phase1_surface_normalize_record_generic_kind_type_tree tree =
          Some refined);
      [ unfold phase1_surface_normalize_record_generic_kind_type_tree;
        rewrite Hbase;
        unfold phase1_surface_normalize_record_generic_kind_type_spine;
        cbn;
        rewrite Hrefined_generic;
        reflexivity
      | exists refined;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_record_generic_kind_type_tree_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Theorem
  phase1_surface_normalize_data_generic_kind_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_data_generic_kind_type_tree tree =
        Some refined /\
      phase1_surface_data_generic_kind_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_data_record_field_type_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  destruct base as
    [name generic_params mode requirements first_variant rest_variants].
  cbn in Hbase, Hbase_round_trip.
  rewrite <- Hbase_round_trip in Hderive.
  unfold phase1_surface_data_record_field_type_spine_tree in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "data_decl"
      input rest
      (PTNonterminal "data_decl"
        (PTSequence
          [ PTLiteral "data";
            phase1_surface_identifier_tree name;
            phase1_surface_optional_generic_params_tree generic_params;
            phase1_surface_optional_mode_tree mode;
            phase1_surface_optional_generic_requirements_tree requirements;
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
          phase1_surface_optional_generic_params_tree generic_params;
          phase1_surface_optional_mode_tree mode;
          phase1_surface_optional_generic_requirements_tree requirements;
          PTLiteral "=";
          phase1_surface_record_field_type_variant_spine_tree first_variant;
          PTRepetition
            (map phase1_surface_record_field_type_data_suffix_tree
              rest_variants);
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
  | Hgeneric : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_params"))
      _ _ (phase1_surface_optional_generic_params_tree generic_params) |- _ =>
      destruct
        (phase1_surface_normalize_optional_generic_params_kind_type_total_from_spine_derivation
          generic_params _ _ _ Hgeneric)
        as [refined_generic Hrefined_generic];
      let refined := constr:(
        {| phase1_data_generic_kind_type_spine_name := name;
           phase1_data_generic_kind_type_spine_generic_params :=
             refined_generic;
           phase1_data_generic_kind_type_spine_mode := mode;
           phase1_data_generic_kind_type_spine_requirements := requirements;
           phase1_data_generic_kind_type_spine_first_variant := first_variant;
           phase1_data_generic_kind_type_spine_rest_variants :=
             rest_variants |}) in
      assert (Hnormalize :
        phase1_surface_normalize_data_generic_kind_type_tree tree =
          Some refined);
      [ unfold phase1_surface_normalize_data_generic_kind_type_tree;
        rewrite Hbase;
        unfold phase1_surface_normalize_data_generic_kind_type_spine;
        cbn;
        rewrite Hrefined_generic;
        reflexivity
      | exists refined;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_data_generic_kind_type_tree_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
