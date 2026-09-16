From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSourceHeader
  GrammarAstSourceHeaderTotality
  GrammarAstTopLevelSpine
  GrammarAstGenericParamsTotality.

From Phil.Surface Require Export
  GrammarAstRecordSpine
  GrammarAstGenericParamsSpine
  GrammarAstStructuralModeSpine.

Import ListNotations.
Open Scope string_scope.

(* Converse for the shared structural-mode correspondence introduced by #943. *)

Definition phase1_surface_structural_mode_items_for_totality
  : list EbnfExpression :=
  [ ELiteral "unrestricted";
    ELiteral "affine";
    ELiteral "linear"
  ].

Lemma phase1_surface_structural_mode_lookup_for_totality :
  lookupRule "structural_mode" phase1_surface_rules =
    Some (EAlternative phase1_surface_structural_mode_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition phase1_surface_structural_mode_expression_for_totality
  (mode : Phase1SurfaceStructuralMode) : EbnfExpression :=
  ELiteral (phase1_surface_structural_mode_literal mode).

Lemma phase1_surface_structural_mode_item_matches_mode :
  forall index item,
    nth_error phase1_surface_structural_mode_items_for_totality index = Some item ->
    exists mode,
      phase1_surface_structural_mode_of_index index = Some mode /\
      item = phase1_surface_structural_mode_expression_for_totality mode.
Proof.
  intros index item Hnth.
  destruct index as [|index]; cbn in Hnth.
  - inversion Hnth; subst item.
    exists Phase1UnrestrictedMode. split; reflexivity.
  - destruct index as [|index]; cbn in Hnth.
    + inversion Hnth; subst item.
      exists Phase1AffineMode. split; reflexivity.
    + destruct index as [|index]; cbn in Hnth.
      * inversion Hnth; subst item.
        exists Phase1LinearMode. split; reflexivity.
      * destruct index; cbn in Hnth; discriminate Hnth.
Qed.

Lemma phase1_surface_normalize_structural_mode_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "structural_mode")
      input rest tree ->
    exists mode,
      phase1_surface_normalize_structural_mode tree = Some mode /\
      phase1_surface_structural_mode_tree mode = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "structural_mode"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_structural_mode_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "structural_mode"))
      phase1_surface_structural_mode_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct
    (phase1_surface_structural_mode_item_matches_mode index item Hnth)
    as [mode [Hmode Hitem]].
  subst item.
  change
    (Derives phase1_surface_rules
      (descend
        (descend path (AtNonterminal "structural_mode"))
        (AtAlternative index))
      (ELiteral (phase1_surface_structural_mode_literal mode))
      input rest selected) in Hselected.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _
      (phase1_surface_structural_mode_literal mode)
      input rest selected Hselected)
    as [tail [_ [_ Hselected_tree]]].
  assert (Hnormalize :
    phase1_surface_normalize_structural_mode tree = Some mode).
  {
    rewrite Htree.
    rewrite Hsubtree.
    rewrite Hselected_tree.
    unfold phase1_surface_normalize_structural_mode,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hmode.
    rewrite String.eqb_refl.
    reflexivity.
  }
  exists mode.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_structural_mode_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_optional_mode_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ELiteral "mode";
            ENonterminal "structural_mode"
          ]))
      input rest tree ->
    exists mode,
      phase1_surface_normalize_optional_mode tree = Some mode /\
      phase1_surface_optional_mode_tree mode = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ESequence
        [ ELiteral "mode";
          ENonterminal "structural_mode"
        ])
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_mode tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_mode_round_trip.
      exact Hnormalize.
  - destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtOptionalBody)
        [ ELiteral "mode";
          ENonterminal "structural_mode"
        ]
        input rest body Hbody)
      as [trees [Hbody_tree Hitems]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules
        (descend path AtOptionalBody) 0
        (ELiteral "mode")
        [ENonterminal "structural_mode"]
        input rest trees Hitems)
      as [after_keyword [keyword_tree [tail_trees
        [Htrees [Hkeyword Htail]]]]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules
        (descend path AtOptionalBody) 1
        (ENonterminal "structural_mode") []
        after_keyword rest tail_trees Htail)
      as [after_mode [mode_tree [nil_trees
        [Htail_trees [Hmode Hnil]]]]].
    rewrite Htrees, Htail_trees in Hbody_tree.
    inversion Hnil; subst nil_trees.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "mode" _ _ keyword_tree Hkeyword)
      as [keyword_tail [_ [_ Hkeyword_tree]]].
    destruct
      (phase1_surface_normalize_structural_mode_total_from_derivation
        _ _ _ mode_tree Hmode)
      as [mode [Hmode_normalize Hmode_round_trip]].
    assert (Hnormalize :
      phase1_surface_normalize_optional_mode tree = Some (Some mode)).
    {
      rewrite Hsome.
      rewrite Hbody_tree.
      rewrite Hkeyword_tree.
      unfold phase1_surface_normalize_optional_mode,
        phase1_surface_expect_optional,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_expect_literal.
      cbn.
      rewrite Hmode_normalize.
      reflexivity.
    }
    exists (Some mode).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_mode_round_trip.
      exact Hnormalize.
Qed.

Lemma phase1_surface_record_decl_mode_lookup_for_totality :
  exists requirements_expr fields_expr,
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
            requirements_expr;
            ELiteral "{";
            fields_expr;
            ELiteral "}"
          ]).
Proof.
  vm_compute.
  do 2 eexists.
  reflexivity.
Qed.

Theorem phase1_surface_normalize_record_mode_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_mode_tree tree = Some refined /\
      phase1_surface_record_mode_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_record_decl_mode_lookup_for_totality
    as [requirements_expr [fields_expr Hlookup_exact]].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "record_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
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
        requirements_expr;
        ELiteral "{";
        fields_expr;
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
              ENonterminal "structural_mode"
            ]);
        requirements_expr;
        ELiteral "{";
        fields_expr;
        ELiteral "}"
      ]
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
              ENonterminal "structural_mode"
            ]);
        requirements_expr;
        ELiteral "{";
        fields_expr;
        ELiteral "}"
      ]
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
              ENonterminal "structural_mode"
            ]);
        requirements_expr;
        ELiteral "{";
        fields_expr;
        ELiteral "}"
      ]
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
            ENonterminal "structural_mode"
          ]))
      [ requirements_expr;
        ELiteral "{";
        fields_expr;
        ELiteral "}"
      ]
      after_generic rest tail3_trees Htail3)
    as [after_mode [mode_tree [tail4_trees
      [Htail3_trees [Hmode Htail4]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 4
      requirements_expr
      [ ELiteral "{";
        fields_expr;
        ELiteral "}"
      ]
      after_mode rest tail4_trees Htail4)
    as [after_requirements [requirements_tree [tail5_trees
      [Htail4_trees [Hrequirements Htail5]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 5
      (ELiteral "{")
      [ fields_expr;
        ELiteral "}"
      ]
      after_requirements rest tail5_trees Htail5)
    as [after_open [open_tree [tail6_trees
      [Htail5_trees [Hopen Htail6]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 6
      fields_expr
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
  pose (refined :=
    {| phase1_record_mode_spine_name := name;
       phase1_record_mode_spine_generic_params := parameters;
       phase1_record_mode_spine_mode := mode;
       phase1_record_mode_spine_requirements_tree := requirements_tree;
       phase1_record_mode_spine_fields_tree := fields_tree |}).
  assert (Hnormalize :
    phase1_surface_normalize_record_mode_tree tree = Some refined).
  {
    unfold phase1_surface_normalize_record_mode_tree.
    rewrite Hgeneric_tree_normalize.
    unfold phase1_surface_normalize_record_mode_spine.
    replace (phase1_record_generic_spine_mode_tree generic_refined)
      with mode_tree.
    - rewrite Hmode_normalize.
      unfold generic_refined, refined.
      reflexivity.
    - unfold generic_refined.
      reflexivity.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_record_mode_tree_round_trip.
    exact Hnormalize.
Qed.
