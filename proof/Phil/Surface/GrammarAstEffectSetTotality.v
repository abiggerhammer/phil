From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetSpine
  GrammarAstGenericRequirementsTotality
  GrammarAstStaticReferenceTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the effect-set structural refinement from #1230. *)

Lemma phase1_surface_effect_set_expression_lookup_for_totality :
  lookupRule "effect_set_expression" phase1_surface_rules =
    Some
      (EAlternative
        [ ENonterminal "effect_set_literal";
          ENonterminal "static_reference"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_effect_set_literal_lookup_for_totality :
  lookupRule "effect_set_literal" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "{";
          EOptional
            (ESequence
              [ ENonterminal "effect_expression";
                ERepetition
                  (ESequence
                    [ ELiteral ",";
                      ENonterminal "effect_expression"
                    ])
              ]);
          ELiteral "}"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_effect_expression_node_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest tree ->
    phase1_surface_normalize_effect_expression_node tree = Some tree.
Proof.
  intros path input rest tree Hderive.
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "effect_expression" path input rest tree Hderive) as Hvalidate.
  unfold phase1_surface_normalize_effect_expression_node.
  rewrite Hvalidate.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_effect_set_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "effect_expression"])
      input rest tree ->
    exists effect,
      phase1_surface_normalize_effect_set_suffix tree = Some effect /\
      phase1_surface_effect_set_suffix_tree effect = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral ",";
        ENonterminal "effect_expression"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral ",")
      [ ENonterminal "effect_expression" ]
      input rest trees Hitems)
    as [after_comma [comma_tree [tail_trees
      [Htrees [Hcomma Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "effect_expression") []
      after_comma rest tail_trees Htail)
    as [after_effect [effect_tree [nil_trees
      [Htail_trees [Heffect Hnil]]]]].
  rewrite Htrees, Htail_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "," _ _ comma_tree Hcomma)
    as [comma_tail [_ [_ Hcomma_tree]]].
  pose proof
    (phase1_surface_normalize_effect_expression_node_total_from_derivation
      _ _ _ effect_tree Heffect) as Heffect_normalize.
  assert (Hnormalize :
    phase1_surface_normalize_effect_set_suffix tree = Some effect_tree).
  {
    rewrite Htree, Hcomma_tree.
    unfold phase1_surface_normalize_effect_set_suffix,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite Heffect_normalize.
    reflexivity.
  }
  exists effect_tree.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_effect_set_suffix_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_effect_set_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body =
      ESequence [ELiteral ","; ENonterminal "effect_expression"] ->
    exists effects,
      phase1_surface_normalize_effect_set_suffixes trees = Some effects.
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
      (phase1_surface_normalize_effect_set_suffix_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [effect [Heffect Heffect_round_trip]].
    destruct (IHrest eq_refl)
      as [effects Heffects].
    exists (effect :: effects).
    cbn.
    rewrite Heffect, Heffects.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_effect_set_entries_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "effect_expression"
                ])
          ]))
      input rest tree ->
    exists effects,
      phase1_surface_normalize_effect_set_entries tree = Some effects /\
      phase1_surface_effect_set_entries_tree effects = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ESequence
        [ ENonterminal "effect_expression";
          ERepetition
            (ESequence
              [ ELiteral ",";
                ENonterminal "effect_expression"
              ])
        ])
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_effect_set_entries tree = Some []).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists [].
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_effect_set_entries_round_trip.
      exact Hnormalize.
  - destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtOptionalBody)
        [ ENonterminal "effect_expression";
          ERepetition
            (ESequence
              [ ELiteral ",";
                ENonterminal "effect_expression"
              ])
        ]
        input rest body Hbody)
      as [trees [Hbody_tree Hitems]].
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules
        (descend path AtOptionalBody) 0
        (ENonterminal "effect_expression")
        [ ERepetition
            (ESequence
              [ ELiteral ",";
                ENonterminal "effect_expression"
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
              ENonterminal "effect_expression"
            ]))
        []
        after_first rest tail_trees Htail)
      as [after_rest [rest_tree [nil_trees
        [Htail_trees [Hrest Hnil]]]]].
    rewrite Htrees, Htail_trees in Hbody_tree.
    inversion Hnil; subst nil_trees.
    pose proof
      (phase1_surface_normalize_effect_expression_node_total_from_derivation
        _ _ _ first_tree Hfirst) as Hfirst_normalize.
    destruct
      (phase1_surface_repetition_derivation_exposes
        _
        (ESequence
          [ ELiteral ",";
            ENonterminal "effect_expression"
          ])
        _ _ rest_tree Hrest)
      as [rest_trees [Hrest_tree Hrest_body]].
    destruct
      (phase1_surface_normalize_effect_set_suffixes_total_from_repetition
        _
        (ESequence
          [ ELiteral ",";
            ENonterminal "effect_expression"
          ])
        _ _ rest_trees Hrest_body eq_refl)
      as [rest_effects Hrest_normalize].
    assert (Hnormalize :
      phase1_surface_normalize_effect_set_entries tree =
        Some (first_tree :: rest_effects)).
    {
      rewrite Hsome, Hbody_tree, Hrest_tree.
      unfold phase1_surface_normalize_effect_set_entries,
        phase1_surface_expect_optional,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_expect_repetition.
      cbn.
      rewrite Hfirst_normalize, Hrest_normalize.
      reflexivity.
    }
    exists (first_tree :: rest_effects).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_effect_set_entries_round_trip.
      exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_effect_set_literal_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_set_literal")
      input rest tree ->
    exists literal,
      phase1_surface_normalize_effect_set_literal_spine tree = Some literal /\
      phase1_surface_effect_set_literal_spine_tree literal = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_set_literal"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_set_literal_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal"))
      [ ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "effect_expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "effect_expression"
                  ])
            ]);
        ELiteral "}"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal")) 0
      (ELiteral "{")
      [ EOptional
          (ESequence
            [ ENonterminal "effect_expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "effect_expression"
                  ])
            ]);
        ELiteral "}"
      ]
      input rest trees Hitems)
    as [after_open [open_tree [tail1
      [Htrees [Hopen Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal")) 1
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "effect_expression"
                ])
          ]))
      [ ELiteral "}" ]
      after_open rest tail1 Htail1)
    as [after_entries [entries_tree [tail2
      [Htail1_trees [Hentries Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal")) 2
      (ELiteral "}") []
      after_entries rest tail2 Htail2)
    as [after_close [close_tree [nil_trees
      [Htail2_trees [Hclose Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "{" _ _ open_tree Hopen)
    as [open_tail [_ [_ Hopen_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "}" _ _ close_tree Hclose)
    as [close_tail [_ [_ Hclose_tree]]].
  destruct
    (phase1_surface_normalize_effect_set_entries_total_from_derivation
      _ _ _ entries_tree Hentries)
    as [effects [Heffects Heffects_round_trip]].
  pose (literal :=
    {| phase1_effect_set_literal_spine_effects := effects |}).
  assert (Hnormalize :
    phase1_surface_normalize_effect_set_literal_spine tree =
      Some literal).
  {
    rewrite Htree, Hsubtree, Hopen_tree, Hclose_tree.
    unfold phase1_surface_normalize_effect_set_literal_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_literal.
    cbn.
    rewrite Heffects.
    reflexivity.
  }
  exists literal.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_effect_set_literal_spine_round_trip.
    exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_effect_set_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest tree ->
    exists effects,
      phase1_surface_normalize_effect_set_spine tree = Some effects /\
      phase1_surface_effect_set_spine_tree effects = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_set_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_set_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_expression"))
      [ ENonterminal "effect_set_literal";
        ENonterminal "static_reference"
      ]
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index]; cbn in Hnth.
  - inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_effect_set_literal_spine_total_from_derivation
        (descend
          (descend path (AtNonterminal "effect_set_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [literal [Hliteral Hliteral_round_trip]].
    pose (effects := Phase1EffectSetLiteral literal).
    assert (Hnormalize :
      phase1_surface_normalize_effect_set_spine tree = Some effects).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_effect_set_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hliteral.
      reflexivity.
    }
    exists effects.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_effect_set_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index]; cbn in Hnth.
    + inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_static_reference_spine_total_from_derivation
          (descend
            (descend path (AtNonterminal "effect_set_expression"))
            (AtAlternative 1))
          input rest selected Hselected)
        as [reference [Hreference Hreference_round_trip]].
      pose (effects := Phase1EffectSetReference reference).
      assert (Hnormalize :
        phase1_surface_normalize_effect_set_spine tree = Some effects).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_effect_set_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite Hreference.
        reflexivity.
      }
      exists effects.
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_effect_set_spine_round_trip.
        exact Hnormalize.
    + destruct index; cbn in Hnth; discriminate Hnth.
Qed.
