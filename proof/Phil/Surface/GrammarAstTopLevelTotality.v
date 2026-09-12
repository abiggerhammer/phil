From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSourceHeader
  GrammarAstSourceHeaderTotality
  GrammarAstTopLevelSpine
  GrammarDeterminacySimpleResolverSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the proof-side top-level correspondence introduced by #929.

  GrammarAstTopLevelSpine proves that every successful top-level normalization
  is lossless.  This file proves that the normalization cannot fail on a tree
  carried by an ordinary certified Grammar-v1 derivation.
*)

Lemma phase1_surface_metadata_string_lookup_for_top_level :
  lookupRule "metadata_string_literal" phase1_surface_rules =
    Some (ELexicalClass "STRING_LITERAL").
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_attribute_lookup_for_top_level :
  lookupRule "attribute" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "@";
          ENonterminal "identifier";
          ELiteral "(";
          ENonterminal "metadata_string_literal";
          ELiteral ")"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_top_level_lookup_for_spine :
  lookupRule "top_level_decl" phase1_surface_rules =
    Some
      (ESequence
        [ ERepetition (ENonterminal "attribute");
          ENonterminal "declaration"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_declaration_items_exact :
  phase1_surface_declaration_items =
    [ ENonterminal "record_decl";
      ENonterminal "data_decl";
      ENonterminal "type_alias_decl";
      ENonterminal "claim_decl";
      ENonterminal "callable_contract_decl";
      ENonterminal "function_decl";
      ENonterminal "provider_contract_decl";
      ENonterminal "provider_implementation_decl";
      ENonterminal "opaque_provider_implementation_decl";
      ENonterminal "protocol_decl";
      ENonterminal "capability_decl";
      ENonterminal "boundary_decl";
      ENonterminal "architecture_decl";
      ENonterminal "component_decl";
      ENonterminal "program_decl"
    ].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_declaration_item_matches_tag :
  forall index item,
    nth_error phase1_surface_declaration_items index = Some item ->
    exists tag,
      phase1_surface_declaration_tag_of_index index = Some tag /\
      item = ENonterminal (phase1_surface_declaration_tag_name tag).
Proof.
  intros index item Hnth.
  rewrite phase1_surface_declaration_items_exact in Hnth.
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    exists Phase1RecordDeclaration. split; reflexivity.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      exists Phase1DataDeclaration. split; reflexivity.
    + destruct index as [|index].
      * cbn in Hnth.
        inversion Hnth; subst item.
        exists Phase1TypeAliasDeclaration. split; reflexivity.
      * destruct index as [|index].
        -- cbn in Hnth.
           inversion Hnth; subst item.
           exists Phase1ClaimDeclaration. split; reflexivity.
        -- destruct index as [|index].
           ++ cbn in Hnth.
              inversion Hnth; subst item.
              exists Phase1CallableContractDeclaration. split; reflexivity.
           ++ destruct index as [|index].
              ** cbn in Hnth.
                 inversion Hnth; subst item.
                 exists Phase1FunctionDeclaration. split; reflexivity.
              ** destruct index as [|index].
                 --- cbn in Hnth.
                     inversion Hnth; subst item.
                     exists Phase1ProviderContractDeclaration. split; reflexivity.
                 --- destruct index as [|index].
                     +++ cbn in Hnth.
                         inversion Hnth; subst item.
                         exists Phase1ProviderImplementationDeclaration.
                         split; reflexivity.
                     +++ destruct index as [|index].
                         *** cbn in Hnth.
                             inversion Hnth; subst item.
                             exists Phase1OpaqueProviderImplementationDeclaration.
                             split; reflexivity.
                         *** destruct index as [|index].
                             ---- cbn in Hnth.
                                  inversion Hnth; subst item.
                                  exists Phase1ProtocolDeclaration.
                                  split; reflexivity.
                             ---- destruct index as [|index].
                                  ++++ cbn in Hnth.
                                       inversion Hnth; subst item.
                                       exists Phase1CapabilityDeclaration.
                                       split; reflexivity.
                                  ++++ destruct index as [|index].
                                       ***** cbn in Hnth.
                                             inversion Hnth; subst item.
                                             exists Phase1BoundaryDeclaration.
                                             split; reflexivity.
                                       ***** destruct index as [|index].
                                             ------ cbn in Hnth.
                                                    inversion Hnth; subst item.
                                                    exists Phase1ArchitectureDeclaration.
                                                    split; reflexivity.
                                             ------ destruct index as [|index].
                                                    ++++++ cbn in Hnth.
                                                           inversion Hnth; subst item.
                                                           exists Phase1ComponentDeclaration.
                                                           split; reflexivity.
                                                    ++++++ destruct index as [|index].
                                                           ******* cbn in Hnth.
                                                                   inversion Hnth; subst item.
                                                                   exists Phase1ProgramDeclaration.
                                                                   split; reflexivity.
                                                           ******* destruct index; cbn in Hnth; discriminate Hnth.
Qed.

Lemma phase1_surface_normalize_metadata_string_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "metadata_string_literal") input rest tree ->
    exists value,
      phase1_surface_normalize_metadata_string tree = Some value.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "metadata_string_literal"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_metadata_string_lookup_for_top_level in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (lexical_derivation_is_exact
      phase1_surface_rules
      (descend path (AtNonterminal "metadata_string_literal"))
      "STRING_LITERAL" input rest subtree Hbody)
    as [value [tail [_ [_ Hsubtree]]]].
  exists value.
  rewrite Htree.
  rewrite Hsubtree.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_attribute_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "attribute")
      input rest tree ->
    exists attribute,
      phase1_surface_normalize_attribute_spine tree = Some attribute.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "attribute"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_attribute_lookup_for_top_level in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "attribute"))
      [ ELiteral "@";
        ENonterminal "identifier";
        ELiteral "(";
        ENonterminal "metadata_string_literal";
        ELiteral ")"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hat : Derives phase1_surface_rules _
      (ELiteral "@") _ _ ?at_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "@" _ _ at_tree Hat)
        as [at_tail [_ [_ Hat_tree]]]
  end.
  match goal with
  | Hopen : Derives phase1_surface_rules _
      (ELiteral "(") _ _ ?open_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "(" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]]
  end.
  match goal with
  | Hclose : Derives phase1_surface_rules _
      (ELiteral ")") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ")" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]]
  end.
  match goal with
  | Hname : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?name_tree |- _ =>
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize]
  end.
  match goal with
  | Hvalue : Derives phase1_surface_rules _
      (ENonterminal "metadata_string_literal") _ _ ?value_tree |- _ =>
      destruct
        (phase1_surface_normalize_metadata_string_total_from_derivation
          _ _ _ value_tree Hvalue)
        as [value Hvalue_normalize]
  end.
  exists
    {| phase1_attribute_spine_name := name;
       phase1_attribute_spine_value := value |}.
  rewrite Hat_tree.
  rewrite Hopen_tree.
  rewrite Hclose_tree.
  unfold phase1_surface_normalize_attribute_spine,
    phase1_surface_expect_nonterminal,
    phase1_surface_expect_sequence,
    phase1_surface_exact5,
    phase1_surface_expect_literal.
  cbn.
  rewrite Hname_normalize.
  rewrite Hvalue_normalize.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_attribute_spines_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ENonterminal "attribute" ->
    exists attributes,
      phase1_surface_normalize_attribute_spines trees = Some attributes.
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
      (phase1_surface_normalize_attribute_spine_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [attribute Htree].
    destruct (IHrest eq_refl) as [attributes Hattributes].
    exists (attribute :: attributes).
    cbn.
    rewrite Htree.
    rewrite Hattributes.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_declaration_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "declaration")
      input rest tree ->
    exists declaration,
      phase1_surface_normalize_declaration_spine tree = Some declaration.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "declaration"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_declaration_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "declaration"))
      phase1_surface_declaration_items
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct
    (phase1_surface_declaration_item_matches_tag index item Hnth)
    as [tag [Htag Hitem]].
  subst item.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "declaration"))
        (AtAlternative index))
      (phase1_surface_declaration_tag_name tag)
      input rest selected Hselected)
    as [selected_body [selected_subtree
        [Hselected_lookup [Hselected_tree Hselected_body]]]].
  exists
    {| phase1_declaration_spine_tag := tag;
       phase1_declaration_spine_selected_tree := selected |}.
  rewrite Htree.
  rewrite Hsubtree.
  rewrite Hselected_tree.
  unfold phase1_surface_normalize_declaration_spine,
    phase1_surface_expect_nonterminal,
    phase1_surface_expect_alternative.
  cbn.
  rewrite Htag.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_top_level_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "top_level_decl")
      input rest tree ->
    exists top_level,
      phase1_surface_normalize_top_level_spine tree = Some top_level.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "top_level_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_top_level_lookup_for_spine in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "top_level_decl"))
      [ ERepetition (ENonterminal "attribute");
        ENonterminal "declaration"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hattributes : Derives phase1_surface_rules _
      (ERepetition (ENonterminal "attribute")) _ _ ?attribute_tree |- _ =>
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ (ENonterminal "attribute")
          _ _ attribute_tree Hattributes)
        as [attribute_trees [Hattribute_tree Hattribute_body]]
  end.
  destruct
    (phase1_surface_normalize_attribute_spines_total_from_repetition
      _ (ENonterminal "attribute")
      _ _ attribute_trees Hattribute_body eq_refl)
    as [attributes Hattributes_normalize].
  match goal with
  | Hdeclaration : Derives phase1_surface_rules _
      (ENonterminal "declaration") _ _ ?declaration_tree |- _ =>
      destruct
        (phase1_surface_normalize_declaration_spine_total_from_derivation
          _ _ _ declaration_tree Hdeclaration)
        as [declaration Hdeclaration_normalize]
  end.
  exists
    {| phase1_top_level_spine_attributes := attributes;
       phase1_top_level_spine_declaration := declaration |}.
  rewrite Hattribute_tree.
  unfold phase1_surface_normalize_top_level_spine,
    phase1_surface_expect_nonterminal,
    phase1_surface_expect_sequence,
    phase1_surface_exact2,
    phase1_surface_expect_repetition.
  cbn.
  rewrite Hattributes_normalize.
  rewrite Hdeclaration_normalize.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_top_level_spines_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ENonterminal "top_level_decl" ->
    exists top_levels,
      phase1_surface_normalize_top_level_spines trees = Some top_levels.
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
      (phase1_surface_normalize_top_level_spine_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [top_level Htree].
    destruct (IHrest eq_refl) as [top_levels Htop_levels].
    exists (top_level :: top_levels).
    cbn.
    rewrite Htree.
    rewrite Htop_levels.
    reflexivity.
Qed.

Theorem phase1_surface_normalize_source_top_level_total :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    exists source,
      phase1_surface_normalize_source_top_level_tree tree = Some source /\
      phase1_surface_source_top_level_tree source = tree.
Proof.
  intros tokens tree Hcomplete.
  unfold Phase1CompleteDerivation, CompleteDerivation in Hcomplete.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules [] phase1_surface_start
      tokens [] tree Hcomplete)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite GrammarAstSourceSpine.phase1_surface_start_rule in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend [] (AtNonterminal phase1_surface_start))
      [ EOptional (ENonterminal "module_decl");
        ERepetition (ENonterminal "import_decl");
        ERepetition (ENonterminal "top_level_decl")
      ]
      tokens [] subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hmodule : Derives phase1_surface_rules _
      (EOptional (ENonterminal "module_decl")) _ _ ?module_part,
    Himports : Derives phase1_surface_rules _
      (ERepetition (ENonterminal "import_decl")) _ _ ?imports_part,
    Htops : Derives phase1_surface_rules _
      (ERepetition (ENonterminal "top_level_decl")) _ _ ?tops_part |- _ =>
      destruct
        (phase1_surface_normalize_optional_module_total_from_derivation
          _ _ _ module_part Hmodule)
        as [module_tree [module_name [Hmodule_tree Hmodule_normalize]]];
      destruct
        (phase1_surface_normalize_import_repetition_total_from_derivation
          _ _ _ imports_part Himports)
        as [import_trees [import_headers [Himports_tree Himports_normalize]]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ (ENonterminal "top_level_decl")
          _ _ tops_part Htops)
        as [top_trees [Htops_tree Htops_body]];
      destruct
        (phase1_surface_normalize_top_level_spines_total_from_repetition
          _ (ENonterminal "top_level_decl")
          _ _ top_trees Htops_body eq_refl)
        as [top_levels Htop_levels_normalize];
      let source := constr:(
        {| phase1_source_top_level_module := module_name;
           phase1_source_top_level_imports := import_headers;
           phase1_source_top_level_declarations := top_levels |}) in
      assert (Hsource_shape :
        tree =
          PTNonterminal phase1_surface_start
            (PTSequence
              [ match module_tree with
                | None => PTOptionalNone
                | Some body => PTOptionalSome body
                end;
                PTRepetition import_trees;
                PTRepetition top_trees
              ])).
      {
        rewrite Htree.
        rewrite Hsubtree.
        rewrite Hmodule_tree.
        rewrite Himports_tree.
        rewrite Htops_tree.
        reflexivity.
      }
      assert (Hnormalize :
        phase1_surface_normalize_source_top_level_tree tree = Some source).
      {
        rewrite Hsource_shape.
        unfold phase1_surface_normalize_source_top_level_tree,
          phase1_surface_normalize_source_header_tree,
          phase1_surface_normalize_source_spine,
          phase1_surface_normalize_source_header,
          phase1_surface_normalize_source_top_level.
        rewrite String.eqb_refl.
        destruct module_tree as [module_body |]; cbn in *.
        - rewrite Hmodule_normalize.
          rewrite Himports_normalize.
          rewrite Htop_levels_normalize.
          reflexivity.
        - rewrite Hmodule_normalize.
          rewrite Himports_normalize.
          rewrite Htop_levels_normalize.
          reflexivity.
      }
      exists source.
      split.
      + exact Hnormalize.
      + eapply phase1_surface_normalize_source_top_level_tree_round_trip.
        exact Hnormalize
  end.
Qed.
