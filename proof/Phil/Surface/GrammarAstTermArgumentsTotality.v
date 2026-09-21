From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermArgumentsSpine
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the reusable term_arguments spine introduced by #1243. *)

Lemma phase1_surface_term_arguments_lookup_for_totality :
  lookupRule "term_arguments" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "(";
          EOptional
            (ESequence
              [ ENonterminal "expression";
                ERepetition
                  (ESequence
                    [ ELiteral ",";
                      ENonterminal "expression"
                    ])
              ]);
          ELiteral ")"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_expression_node_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest tree ->
    phase1_surface_normalize_expression_node tree = Some tree.
Proof.
  intros path input rest tree Hderive.
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "expression" path input rest tree Hderive) as Hvalidate.
  unfold phase1_surface_normalize_expression_node.
  rewrite Hvalidate.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_term_argument_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "expression"])
      input rest tree ->
    exists argument,
      phase1_surface_normalize_term_argument_suffix tree = Some argument /\
      phase1_surface_term_argument_suffix_tree argument = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral ",";
        ENonterminal "expression"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral ",")
      [ ENonterminal "expression" ]
      input rest trees Hitems)
    as [after_comma [comma_tree [tail_trees
      [Htrees [Hcomma Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "expression") []
      after_comma rest tail_trees Htail)
    as [after_argument [argument_tree [nil_trees
      [Htail_trees [Hargument Hnil]]]]].
  rewrite Htrees, Htail_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "," _ _ comma_tree Hcomma)
    as [comma_tail [_ [_ Hcomma_tree]]].
  pose proof
    (phase1_surface_normalize_expression_node_total_from_derivation
      _ _ _ argument_tree Hargument) as Hargument_normalize.
  assert (Hnormalize :
    phase1_surface_normalize_term_argument_suffix tree =
      Some argument_tree).
  {
    rewrite Htree, Hcomma_tree.
    unfold phase1_surface_normalize_term_argument_suffix,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hargument_normalize.
    reflexivity.
  }
  exists argument_tree.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_term_argument_suffix_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_term_argument_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral ","; ENonterminal "expression"] ->
    exists arguments,
      phase1_surface_normalize_term_argument_suffixes trees =
        Some arguments.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [].
    reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_term_argument_suffix_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hitem)
      as [argument [Hargument Hargument_round_trip]].
    destruct (IHrest eq_refl)
      as [arguments Harguments].
    exists (argument :: arguments).
    cbn.
    rewrite Hargument, Harguments.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_term_argument_entries_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ])
          ]))
      input rest tree ->
    exists arguments,
      phase1_surface_normalize_term_argument_entries tree = Some arguments /\
      phase1_surface_term_argument_entries_tree arguments = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ESequence
        [ ENonterminal "expression";
          ERepetition
            (ESequence
              [ ELiteral ",";
                ENonterminal "expression"
              ])
        ])
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_term_argument_entries tree = Some []).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists [].
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_term_argument_entries_round_trip.
      exact Hnormalize.
  - destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtOptionalBody)
        [ ENonterminal "expression";
          ERepetition
            (ESequence
              [ ELiteral ",";
                ENonterminal "expression"
              ])
        ]
        input rest body Hbody)
      as [trees [Hbody_tree Hitems]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules
        (descend path AtOptionalBody) 0
        (ENonterminal "expression")
        [ ERepetition
            (ESequence
              [ ELiteral ",";
                ENonterminal "expression"
              ])
        ]
        input rest trees Hitems)
      as [after_first [first_tree [tail_trees
        [Htrees [Hfirst Htail]]]]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules
        (descend path AtOptionalBody) 1
        (ERepetition
          (ESequence
            [ ELiteral ",";
              ENonterminal "expression"
            ]))
        []
        after_first rest tail_trees Htail)
      as [after_rest [rest_tree [nil_trees
        [Htail_trees [Hrest Hnil]]]]].
    rewrite Htrees, Htail_trees in Hbody_tree.
    inversion Hnil; subst nil_trees.
    pose proof
      (phase1_surface_normalize_expression_node_total_from_derivation
        _ _ _ first_tree Hfirst) as Hfirst_normalize.
    destruct
      (phase1_surface_repetition_derivation_exposes
        _
        (ESequence
          [ ELiteral ",";
            ENonterminal "expression"
          ])
        _ _ rest_tree Hrest)
      as [rest_trees [Hrest_tree Hrest_body]].
    destruct
      (phase1_surface_normalize_term_argument_suffixes_total_from_repetition
        _
        (ESequence
          [ ELiteral ",";
            ENonterminal "expression"
          ])
        _ _ rest_trees Hrest_body eq_refl)
      as [rest_arguments Hrest_normalize].
    assert (Hnormalize :
      phase1_surface_normalize_term_argument_entries tree =
        Some (first_tree :: rest_arguments)).
    {
      rewrite Hsome, Hbody_tree, Hrest_tree.
      unfold phase1_surface_normalize_term_argument_entries,
        phase1_surface_expect_optional,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_expect_repetition.
      cbn.
      rewrite Hfirst_normalize, Hrest_normalize.
      reflexivity.
    }
    exists (first_tree :: rest_arguments).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_term_argument_entries_round_trip.
      exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_term_arguments_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "term_arguments")
      input rest tree ->
    exists arguments,
      phase1_surface_normalize_term_arguments_spine tree = Some arguments /\
      phase1_surface_term_arguments_spine_tree arguments = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "term_arguments"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_term_arguments_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "term_arguments"))
      [ ELiteral "(";
        EOptional
          (ESequence
            [ ENonterminal "expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
            ]);
        ELiteral ")"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "term_arguments")) 0
      (ELiteral "(")
      [ EOptional
          (ESequence
            [ ENonterminal "expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
            ]);
        ELiteral ")"
      ]
      input rest trees Hitems)
    as [after_open [open_tree [tail1
      [Htrees [Hopen Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "term_arguments")) 1
      (EOptional
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ])
          ]))
      [ ELiteral ")" ]
      after_open rest tail1 Htail1)
    as [after_entries [entries_tree [tail2
      [Htail1_trees [Hentries Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "term_arguments")) 2
      (ELiteral ")") []
      after_entries rest tail2 Htail2)
    as [after_close [close_tree [nil_trees
      [Htail2_trees [Hclose Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "(" _ _ open_tree Hopen)
    as [open_tail [_ [_ Hopen_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ")" _ _ close_tree Hclose)
    as [close_tail [_ [_ Hclose_tree]]].
  destruct
    (phase1_surface_normalize_term_argument_entries_total_from_derivation
      _ _ _ entries_tree Hentries)
    as [values [Hvalues Hvalues_round_trip]].
  pose (arguments :=
    {| phase1_term_arguments_spine_arguments := values |}).
  assert (Hnormalize :
    phase1_surface_normalize_term_arguments_spine tree = Some arguments).
  {
    rewrite Htree, Hsubtree, Hopen_tree, Hclose_tree.
    unfold phase1_surface_normalize_term_arguments_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hvalues.
    reflexivity.
  }
  exists arguments.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_term_arguments_spine_round_trip.
    exact Hnormalize.
Qed.
