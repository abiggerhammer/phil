From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordSpine
  GrammarAstTopLevelTotality
  GrammarDeterminacySimpleResolverSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the proof-side record spine introduced by #934.

  GrammarAstRecordSpine proves that successful normalization of the outer
  record_decl shape is lossless.  This file proves that normalization cannot
  fail on an ordinary certified Grammar-v1 derivation of record_decl.  Shared
  generic/mode/requirement/field payloads remain opaque ParseTree values here.
*)

Lemma phase1_surface_record_decl_lookup_for_totality :
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
          EOptional
            (ESequence
              [ ENonterminal "field_decl";
                ERepetition
                  (ESequence
                    [ ELiteral ",";
                      ENonterminal "field_decl"
                    ]);
                EOptional (ELiteral ",")
              ]);
          ELiteral "}"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma derives_sequence_cons_exposes_head_exact :
  forall rules path index item items input rest trees,
    DerivesSequence rules path index (item :: items) input rest trees ->
    exists middle tree tail_trees,
      trees = tree :: tail_trees /\
      Derives rules (descend path (AtSequence index))
        item input middle tree /\
      DerivesSequence rules path (S index)
        items middle rest tail_trees.
Proof.
  intros rules path index item items input rest trees Hderive.
  inversion Hderive; subst.
  do 3 eexists.
  repeat split; eauto.
Qed.

Theorem phase1_surface_normalize_record_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists record,
      phase1_surface_normalize_record_spine tree = Some record /\
      phase1_surface_record_spine_tree record = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "record_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_record_decl_lookup_for_totality in Hlookup.
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
        EOptional
          (ESequence
            [ ENonterminal "field_decl";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "field_decl"
                  ]);
              EOptional (ELiteral ",")
            ]);
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
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "field_decl";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "field_decl"
                  ]);
              EOptional (ELiteral ",")
            ]);
        ELiteral "}"
      ]
      input rest trees Hitems)
    as [middle0 [keyword_tree [trees1 [Htrees0 [Hkeyword Hitems1]]]]].
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
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "field_decl";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "field_decl"
                  ]);
              EOptional (ELiteral ",")
            ]);
        ELiteral "}"
      ]
      middle0 rest trees1 Hitems1)
    as [middle1 [name_tree [trees2 [Htrees1 [Hname Hitems2]]]]].
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
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "field_decl";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "field_decl"
                  ]);
              EOptional (ELiteral ",")
            ]);
        ELiteral "}"
      ]
      middle1 rest trees2 Hitems2)
    as [middle2 [generic_tree [trees3 [Htrees2 [Hgeneric Hitems3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 3
      (EOptional
        (ESequence
          [ ELiteral "mode";
            ENonterminal "structural_mode"
          ]))
      [ EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "field_decl";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "field_decl"
                  ]);
              EOptional (ELiteral ",")
            ]);
        ELiteral "}"
      ]
      middle2 rest trees3 Hitems3)
    as [middle3 [mode_tree [trees4 [Htrees3 [Hmode Hitems4]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 4
      (EOptional (ENonterminal "generic_requirements"))
      [ ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "field_decl";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "field_decl"
                  ]);
              EOptional (ELiteral ",")
            ]);
        ELiteral "}"
      ]
      middle3 rest trees4 Hitems4)
    as [middle4 [requirements_tree [trees5 [Htrees4 [Hrequirements Hitems5]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 5
      (ELiteral "{")
      [ EOptional
          (ESequence
            [ ENonterminal "field_decl";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "field_decl"
                  ]);
              EOptional (ELiteral ",")
            ]);
        ELiteral "}"
      ]
      middle4 rest trees5 Hitems5)
    as [middle5 [open_tree [trees6 [Htrees5 [Hopen Hitems6]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 6
      (EOptional
        (ESequence
          [ ENonterminal "field_decl";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "field_decl"
                ]);
            EOptional (ELiteral ",")
          ]))
      [ ELiteral "}" ]
      middle5 rest trees6 Hitems6)
    as [middle6 [fields_tree [trees7 [Htrees6 [Hfields Hitems7]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl")) 7
      (ELiteral "}") []
      middle6 rest trees7 Hitems7)
    as [middle7 [close_tree [trees8 [Htrees7 [Hclose Hitems8]]]]].
  rewrite Hsubtree in Htree.
  rewrite Htrees0, Htrees1, Htrees2, Htrees3,
    Htrees4, Htrees5, Htrees6, Htrees7 in Htree.
  inversion Hitems8; subst.
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
  exists
    {| phase1_record_spine_name := name;
       phase1_record_spine_generic_params_tree := generic_tree;
       phase1_record_spine_mode_tree := mode_tree;
       phase1_record_spine_requirements_tree := requirements_tree;
       phase1_record_spine_fields_tree := fields_tree |}.
  split.
  - rewrite Htree, Hkeyword_tree, Hopen_tree, Hclose_tree.
    unfold phase1_surface_normalize_record_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact8,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hname_normalize.
    reflexivity.
  - eapply phase1_surface_normalize_record_spine_round_trip.
    rewrite Htree, Hkeyword_tree, Hopen_tree, Hclose_tree.
    unfold phase1_surface_normalize_record_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact8,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hname_normalize.
    reflexivity.
Qed.
