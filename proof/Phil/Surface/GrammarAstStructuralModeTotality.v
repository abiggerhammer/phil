From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStructuralModeSpine
  GrammarAstGenericParamsTotality.

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
      * discriminate Hnth.
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
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Hkeyword : Derives phase1_surface_rules _
        (ELiteral "mode") _ _ ?keyword_tree,
      Hmode : Derives phase1_surface_rules _
        (ENonterminal "structural_mode") _ _ ?mode_tree |- _ =>
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules _ "mode" _ _ keyword_tree Hkeyword)
          as [keyword_tail [_ [_ Hkeyword_tree]]];
        destruct
          (phase1_surface_normalize_structural_mode_total_from_derivation
            _ _ _ mode_tree Hmode)
          as [mode [Hmode_normalize Hmode_round_trip]];
        assert (Hnormalize :
          phase1_surface_normalize_optional_mode tree = Some (Some mode));
        [ rewrite Hsome;
          rewrite Hbody_tree;
          rewrite Hkeyword_tree;
          unfold phase1_surface_normalize_optional_mode,
            phase1_surface_expect_optional,
            phase1_surface_expect_sequence,
            phase1_surface_exact2,
            phase1_surface_expect_literal;
          cbn;
          rewrite Hmode_normalize;
          reflexivity
        | exists (Some mode);
          split;
          [ exact Hnormalize
          | eapply phase1_surface_normalize_optional_mode_round_trip;
            exact Hnormalize ] ]
    end.
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
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "record") _ _ ?keyword_tree,
    Hname : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?name_tree,
    Hgeneric : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_params")) _ _ ?generic_tree,
    Hmode : Derives phase1_surface_rules _
      (EOptional
        (ESequence
          [ ELiteral "mode";
            ENonterminal "structural_mode"
          ])) _ _ ?mode_tree,
    Hrequirements : Derives phase1_surface_rules _
      requirements_expr _ _ ?requirements_tree,
    Hopen : Derives phase1_surface_rules _
      (ELiteral "{") _ _ ?open_tree,
    Hfields : Derives phase1_surface_rules _
      fields_expr _ _ ?fields_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "}") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "record" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "{" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "}" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      destruct
        (phase1_surface_normalize_optional_generic_params_total_from_derivation
          _ _ _ generic_tree Hgeneric)
        as [parameters [Hgeneric_normalize Hgeneric_round_trip]];
      destruct
        (phase1_surface_normalize_optional_mode_total_from_derivation
          _ _ _ mode_tree Hmode)
        as [mode [Hmode_normalize Hmode_round_trip]];
      let refined := constr:(
        {| phase1_record_mode_spine_name := name;
           phase1_record_mode_spine_generic_params := parameters;
           phase1_record_mode_spine_mode := mode;
           phase1_record_mode_spine_requirements_tree := requirements_tree;
           phase1_record_mode_spine_fields_tree := fields_tree |}) in
      assert (Hnormalize :
        phase1_surface_normalize_record_mode_tree tree = Some refined).
      {
        rewrite Htree.
        rewrite Hsubtree.
        rewrite Hkeyword_tree.
        rewrite Hopen_tree.
        rewrite Hclose_tree.
        unfold phase1_surface_normalize_record_mode_tree,
          phase1_surface_normalize_record_generic_tree,
          phase1_surface_normalize_record_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact8,
          phase1_surface_expect_literal,
          phase1_surface_normalize_record_generic_spine,
          phase1_surface_normalize_record_mode_spine.
        cbn.
        rewrite Hname_normalize.
        rewrite Hgeneric_normalize.
        rewrite Hmode_normalize.
        reflexivity.
      }
      exists refined.
      split.
      + exact Hnormalize.
      + eapply phase1_surface_normalize_record_mode_tree_round_trip.
        exact Hnormalize
  end.
Qed.
