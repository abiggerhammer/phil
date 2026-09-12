From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSourceHeader
  GrammarDeterminacySimpleResolverSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the proof-side source-header correspondence introduced by #926.

  GrammarAstSourceHeader proves that every successful normalization is
  lossless.  This file proves that the normalization cannot fail on a tree
  carried by an ordinary certified Grammar-v1 derivation.
*)

Lemma phase1_surface_repetition_derivation_exposes :
  forall path body input rest tree,
    Derives phase1_surface_rules path (ERepetition body)
      input rest tree ->
    exists trees,
      tree = PTRepetition trees /\
      DerivesRepetition phase1_surface_rules path body
        input rest trees.
Proof.
  intros path body input rest tree Hderive.
  inversion Hderive; subst.
  eexists.
  split; eauto.
Qed.

Lemma phase1_surface_qualified_name_lookup_for_header :
  lookupRule "qualified_name" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "identifier";
          ERepetition
            (ESequence [ELiteral "."; ENonterminal "identifier"])
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_identifier_list_lookup_for_header :
  lookupRule "identifier_list" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "identifier";
          ERepetition
            (ESequence [ELiteral ","; ENonterminal "identifier"])
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_module_decl_lookup_for_header :
  lookupRule "module_decl" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "module";
          ENonterminal "qualified_name";
          ELiteral ";"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_import_decl_lookup_for_header :
  lookupRule "import_decl" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "import";
          ENonterminal "qualified_name";
          EOptional
            (ESequence
              [ ELiteral "{";
                ENonterminal "identifier_list";
                ELiteral "}"
              ]);
          ELiteral ";"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_identifier_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "identifier")
      input rest tree ->
    exists value,
      phase1_surface_normalize_identifier tree = Some value.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "identifier"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_identifier_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (lexical_derivation_is_exact
      phase1_surface_rules
      (descend path (AtNonterminal "identifier"))
      "IDENTIFIER" input rest subtree Hbody)
    as [value [tail [_ [_ Hsubtree]]]].
  exists value.
  rewrite Htree.
  rewrite Hsubtree.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_name_suffix_total_from_derivation :
  forall separator path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral separator; ENonterminal "identifier"])
      input rest tree ->
    exists value,
      phase1_surface_normalize_name_suffix separator tree = Some value.
Proof.
  intros separator path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral separator; ENonterminal "identifier"]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  inversion Hitems as
    [| path0 index0 item0 items0 input0 middle0 rest0
       literal_tree tail_trees Hliteral Htail]; subst.
  inversion Htail as
    [| path1 index1 item1 items1 input1 middle1 rest1
       identifier_tree nil_trees Hidentifier Hnil]; subst.
  inversion Hnil; subst.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ separator _ _ literal_tree Hliteral)
    as [tail [_ [_ Hliteral_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ identifier_tree Hidentifier)
    as [value Hidentifier_normalize].
  exists value.
  rewrite Hliteral_tree.
  unfold phase1_surface_normalize_name_suffix,
    phase1_surface_expect_sequence,
    phase1_surface_exact2,
    phase1_surface_expect_literal.
  cbn.
  rewrite String.eqb_refl.
  exact Hidentifier_normalize.
Qed.

Lemma phase1_surface_normalize_name_suffixes_total_from_repetition :
  forall separator path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral separator; ENonterminal "identifier"] ->
    exists values,
      phase1_surface_normalize_name_suffixes separator trees = Some values.
Proof.
  intros separator path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [].
    reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_name_suffix_total_from_derivation
        separator (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [value Htree].
    destruct (IHrest eq_refl) as [values Hvalues].
    exists (value :: values).
    cbn.
    rewrite Htree.
    rewrite Hvalues.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_name_list_total_from_derivation :
  forall nonterminal separator path input rest tree,
    lookupRule nonterminal phase1_surface_rules =
      Some
        (ESequence
          [ ENonterminal "identifier";
            ERepetition
              (ESequence
                [ELiteral separator; ENonterminal "identifier"])
          ]) ->
    Derives phase1_surface_rules path (ENonterminal nonterminal)
      input rest tree ->
    exists names,
      phase1_surface_normalize_name_list
        nonterminal separator tree = Some names.
Proof.
  intros nonterminal separator path input rest tree Hlookup_exact Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path nonterminal
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal nonterminal))
      [ ENonterminal "identifier";
        ERepetition
          (ESequence [ELiteral separator; ENonterminal "identifier"])
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  inversion Hitems as
    [| path0 index0 item0 items0 input0 middle0 rest0
       identifier_tree tail_trees Hidentifier Htail]; subst.
  inversion Htail as
    [| path1 index1 item1 items1 input1 middle1 rest1
       repetition_tree nil_trees Hrepetition Hnil]; subst.
  inversion Hnil; subst.
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ identifier_tree Hidentifier)
    as [first_value Hfirst].
  destruct
    (phase1_surface_repetition_derivation_exposes
      _
      (ESequence [ELiteral separator; ENonterminal "identifier"])
      _ _ repetition_tree Hrepetition)
    as [suffix_trees [Hrepetition_tree Hrepetition_body]].
  destruct
    (phase1_surface_normalize_name_suffixes_total_from_repetition
      separator _
      (ESequence [ELiteral separator; ENonterminal "identifier"])
      _ _ suffix_trees Hrepetition_body eq_refl)
    as [rest_values Hrest].
  exists
    {| phase1_name_list_first := first_value;
       phase1_name_list_rest := rest_values |}.
  rewrite Hrepetition_tree.
  unfold phase1_surface_normalize_name_list,
    phase1_surface_expect_nonterminal,
    phase1_surface_expect_sequence,
    phase1_surface_exact2,
    phase1_surface_expect_repetition.
  cbn.
  rewrite String.eqb_refl.
  rewrite Hfirst.
  rewrite Hrest.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_qualified_name_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "qualified_name")
      input rest tree ->
    exists names,
      phase1_surface_normalize_qualified_name tree = Some names.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_normalize_qualified_name.
  eapply phase1_surface_normalize_name_list_total_from_derivation.
  - exact phase1_surface_qualified_name_lookup_for_header.
  - exact Hderive.
Qed.

Lemma phase1_surface_normalize_identifier_list_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "identifier_list")
      input rest tree ->
    exists names,
      phase1_surface_normalize_identifier_list tree = Some names.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_normalize_identifier_list.
  eapply phase1_surface_normalize_name_list_total_from_derivation.
  - exact phase1_surface_identifier_list_lookup_for_header.
  - exact Hderive.
Qed.

Lemma phase1_surface_normalize_module_decl_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "module_decl")
      input rest tree ->
    exists name,
      phase1_surface_normalize_module_decl tree = Some name.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "module_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_module_decl_lookup_for_header in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "module_decl"))
      [ ELiteral "module";
        ENonterminal "qualified_name";
        ELiteral ";"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  inversion Hitems as
    [| path0 index0 item0 items0 input0 middle0 rest0
       keyword_tree tail1 Hkeyword Htail1]; subst.
  inversion Htail1 as
    [| path1 index1 item1 items1 input1 middle1 rest1
       name_tree tail2 Hname Htail2]; subst.
  inversion Htail2 as
    [| path2 index2 item2 items2 input2 middle2 rest2
       terminator_tree nil_trees Hterminator Hnil]; subst.
  inversion Hnil; subst.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "module" _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
    as [terminator_tail [_ [_ Hterminator_tree]]].
  destruct
    (phase1_surface_normalize_qualified_name_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  exists name.
  rewrite Hkeyword_tree.
  rewrite Hterminator_tree.
  unfold phase1_surface_normalize_module_decl,
    phase1_surface_expect_nonterminal,
    phase1_surface_expect_sequence,
    phase1_surface_exact3,
    phase1_surface_expect_literal.
  cbn.
  exact Hname_normalize.
Qed.

Lemma phase1_surface_normalize_import_selection_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ELiteral "{";
            ENonterminal "identifier_list";
            ELiteral "}"
          ]))
      input rest tree ->
    exists selection,
      phase1_surface_normalize_import_selection tree = Some selection.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ESequence
        [ ELiteral "{";
          ENonterminal "identifier_list";
          ELiteral "}"
        ])
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - subst tree.
    exists None.
    reflexivity.
  - destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtOptionalBody)
        [ ELiteral "{";
          ENonterminal "identifier_list";
          ELiteral "}"
        ]
        input rest body Hbody)
      as [trees [Hsequence Hitems]].
    inversion Hitems as
      [| path0 index0 item0 items0 input0 middle0 rest0
         open_tree tail1 Hopen Htail1]; subst.
    inversion Htail1 as
      [| path1 index1 item1 items1 input1 middle1 rest1
         identifiers_tree tail2 Hidentifiers Htail2]; subst.
    inversion Htail2 as
      [| path2 index2 item2 items2 input2 middle2 rest2
         close_tree nil_trees Hclose Hnil]; subst.
    inversion Hnil; subst.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "{" _ _ open_tree Hopen)
      as [open_tail [_ [_ Hopen_tree]]].
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "}" _ _ close_tree Hclose)
      as [close_tail [_ [_ Hclose_tree]]].
    destruct
      (phase1_surface_normalize_identifier_list_total_from_derivation
        _ _ _ identifiers_tree Hidentifiers)
      as [identifiers Hidentifiers_normalize].
    exists (Some identifiers).
    rewrite Hopen_tree.
    rewrite Hclose_tree.
    unfold phase1_surface_normalize_import_selection,
      phase1_surface_expect_optional,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hidentifiers_normalize.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_import_decl_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "import_decl")
      input rest tree ->
    exists import_header,
      phase1_surface_normalize_import_decl tree = Some import_header.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "import_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_import_decl_lookup_for_header in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "import_decl"))
      [ ELiteral "import";
        ENonterminal "qualified_name";
        EOptional
          (ESequence
            [ ELiteral "{";
              ENonterminal "identifier_list";
              ELiteral "}"
            ]);
        ELiteral ";"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  inversion Hitems as
    [| path0 index0 item0 items0 input0 middle0 rest0
       keyword_tree tail1 Hkeyword Htail1]; subst.
  inversion Htail1 as
    [| path1 index1 item1 items1 input1 middle1 rest1
       name_tree tail2 Hname Htail2]; subst.
  inversion Htail2 as
    [| path2 index2 item2 items2 input2 middle2 rest2
       selection_tree tail3 Hselection Htail3]; subst.
  inversion Htail3 as
    [| path3 index3 item3 items3 input3 middle3 rest3
       terminator_tree nil_trees Hterminator Hnil]; subst.
  inversion Hnil; subst.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "import" _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
    as [terminator_tail [_ [_ Hterminator_tree]]].
  destruct
    (phase1_surface_normalize_qualified_name_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  destruct
    (phase1_surface_normalize_import_selection_total_from_derivation
      _ _ _ selection_tree Hselection)
    as [selection Hselection_normalize].
  exists
    {| phase1_import_header_name := name;
       phase1_import_header_selection := selection |}.
  rewrite Hkeyword_tree.
  rewrite Hterminator_tree.
  unfold phase1_surface_normalize_import_decl,
    phase1_surface_expect_nonterminal,
    phase1_surface_expect_sequence,
    phase1_surface_exact4,
    phase1_surface_expect_literal.
  cbn.
  rewrite Hname_normalize.
  rewrite Hselection_normalize.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_import_decls_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ENonterminal "import_decl" ->
    exists import_headers,
      phase1_surface_normalize_import_decls trees = Some import_headers.
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
      (phase1_surface_normalize_import_decl_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [import_header Htree].
    destruct (IHrest eq_refl) as [import_headers Hheaders].
    exists (import_header :: import_headers).
    cbn.
    rewrite Htree.
    rewrite Hheaders.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_optional_module_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "module_decl"))
      input rest tree ->
    exists module_tree module_name,
      tree =
        match module_tree with
        | None => PTOptionalNone
        | Some body => PTOptionalSome body
        end /\
      phase1_surface_normalize_optional_module module_tree =
        Some module_name.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "module_decl")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - exists None, None.
    split.
    + exact Hnone.
    + reflexivity.
  - destruct
      (phase1_surface_normalize_module_decl_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [name Hname].
    exists (Some body), (Some name).
    split.
    + exact Hsome.
    + cbn.
      rewrite Hname.
      reflexivity.
Qed.

Lemma phase1_surface_normalize_import_repetition_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ERepetition (ENonterminal "import_decl"))
      input rest tree ->
    exists import_trees import_headers,
      tree = PTRepetition import_trees /\
      phase1_surface_normalize_import_decls import_trees =
        Some import_headers.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_repetition_derivation_exposes
      path (ENonterminal "import_decl")
      input rest tree Hderive)
    as [import_trees [Htree Hrepetition]].
  destruct
    (phase1_surface_normalize_import_decls_total_from_repetition
      path (ENonterminal "import_decl")
      input rest import_trees Hrepetition eq_refl)
    as [import_headers Hnormalize].
  exists import_trees, import_headers.
  split; assumption.
Qed.

Theorem phase1_surface_normalize_source_header_total :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    exists header,
      phase1_surface_normalize_source_header_tree tree = Some header /\
      phase1_surface_source_header_tree header = tree.
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
  inversion Hitems as
    [| path0 index0 item0 items0 input0 middle0 rest0
       module_part tail1 Hmodule Htail1]; subst.
  inversion Htail1 as
    [| path1 index1 item1 items1 input1 middle1 rest1
       imports_part tail2 Himports Htail2]; subst.
  inversion Htail2 as
    [| path2 index2 item2 items2 input2 middle2 rest2
       tops_part nil_trees Htops Hnil]; subst.
  inversion Hnil; subst.
  destruct
    (phase1_surface_normalize_optional_module_total_from_derivation
      _ _ _ module_part Hmodule)
    as [module_tree [module_name [Hmodule_tree Hmodule_normalize]]].
  destruct
    (phase1_surface_normalize_import_repetition_total_from_derivation
      _ _ _ imports_part Himports)
    as [import_trees [import_headers [Himports_tree Himports_normalize]]].
  destruct
    (phase1_surface_repetition_derivation_exposes
      _ (ENonterminal "top_level_decl")
      _ _ tops_part Htops)
    as [top_trees [Htops_tree Htops_body]].
  exists
    {| phase1_source_header_module := module_name;
       phase1_source_header_imports := import_headers;
       phase1_source_header_top_levels := top_trees |}.
  assert (Hnormalize :
    phase1_surface_normalize_source_header_tree
      (PTNonterminal phase1_surface_start
        (PTSequence [module_part; imports_part; tops_part])) =
    Some
      {| phase1_source_header_module := module_name;
         phase1_source_header_imports := import_headers;
         phase1_source_header_top_levels := top_trees |}).
  {
    rewrite Hmodule_tree.
    rewrite Himports_tree.
    rewrite Htops_tree.
    unfold phase1_surface_normalize_source_header_tree,
      phase1_surface_normalize_source_spine,
      phase1_surface_normalize_source_header.
    rewrite String.eqb_refl.
    destruct module_tree as [module_body |]; cbn in *.
    + rewrite Hmodule_normalize.
      rewrite Himports_normalize.
      reflexivity.
    + rewrite Hmodule_normalize.
      rewrite Himports_normalize.
      reflexivity.
  }
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_source_header_tree_round_trip.
    exact Hnormalize.
Qed.
