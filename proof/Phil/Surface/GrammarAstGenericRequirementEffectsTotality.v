From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementEffectsSpine
  GrammarAstGenericRequirementPropositionTotality
  GrammarAstEffectSetTermArgumentsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the generic-requirement effects refinement from #1258. *)

Lemma phase1_surface_normalize_effects_requirement_payload_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral "effects";
          ENonterminal "identifier";
          ELiteral "within";
          ENonterminal "effect_set_expression";
          ELiteral ";"
        ])
      input rest tree ->
    exists name_tree effects,
      phase1_surface_normalize_effects_requirement_payload tree =
        Some (name_tree, effects).
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "effects";
        ENonterminal "identifier";
        ELiteral "within";
        ENonterminal "effect_set_expression";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral "effects")
      [ ENonterminal "identifier";
        ELiteral "within";
        ENonterminal "effect_set_expression";
        ELiteral ";"
      ]
      input rest trees Hitems)
    as [after_keyword [keyword_tree [tail1
      [Htrees [Hkeyword Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "identifier")
      [ ELiteral "within";
        ENonterminal "effect_set_expression";
        ELiteral ";"
      ]
      after_keyword rest tail1 Htail1)
    as [after_name [name_tree [tail2
      [Htail1_trees [Hname Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (ELiteral "within")
      [ ENonterminal "effect_set_expression";
        ELiteral ";"
      ]
      after_name rest tail2 Htail2)
    as [after_within [within_tree [tail3
      [Htail2_trees [Hwithin Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 3
      (ENonterminal "effect_set_expression")
      [ ELiteral ";" ]
      after_within rest tail3 Htail3)
    as [after_effects [effects_tree [tail4
      [Htail3_trees [Heffects Htail4]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 4
      (ELiteral ";") []
      after_effects rest tail4 Htail4)
    as [after_terminator [terminator_tree [nil_trees
      [Htail4_trees [Hterminator Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees,
    Htail4_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "effects" _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "within" _ _ within_tree Hwithin)
    as [within_tail [_ [_ Hwithin_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
    as [terminator_tail [_ [_ Hterminator_tree]]].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "identifier" _ _ _ name_tree Hname) as Hname_validate.
  destruct
    (phase1_surface_normalize_effect_set_term_arguments_tree_total_from_derivation
      _ _ _ effects_tree Heffects)
    as [effects [Heffects_normalize Heffects_round_trip]].
  exists name_tree, effects.
  rewrite Htree, Hkeyword_tree, Hwithin_tree, Hterminator_tree.
  unfold phase1_surface_normalize_effects_requirement_payload,
    phase1_surface_expect_sequence,
    phase1_surface_exact5,
    phase1_surface_expect_literal.
  cbn.
  rewrite String.eqb_refl.
  rewrite Hname_validate.
  rewrite Heffects_normalize.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirement_effects_spine_total_from_spine_derivation :
  forall requirement path input rest,
    Derives phase1_surface_rules path
      (ENonterminal "generic_requirement")
      input rest
      (phase1_surface_generic_requirement_proposition_spine_tree requirement) ->
    exists refined,
      phase1_surface_normalize_generic_requirement_effects_spine requirement =
        Some refined.
Proof.
  intros requirement path input rest Hderive.
  destruct requirement; cbn in Hderive |- *.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules path "generic_requirement"
        input rest
        (PTNonterminal "generic_requirement"
          (PTAlternative 6 selected))
        Hderive)
      as [body [subtree [Hlookup [Htree Hbody]]]].
    rewrite phase1_surface_generic_requirement_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    inversion Htree; subst subtree.
    destruct
      (alternative_derivation_names_exact_branch
        phase1_surface_rules
        (descend path (AtNonterminal "generic_requirement"))
        phase1_surface_generic_requirement_items_for_totality
        input rest
        (PTAlternative 6 selected)
        Hbody)
      as [index [item [selected_tree
        [Hnth [Hselected_tree Hselected]]]]].
    inversion Hselected_tree; subst index selected_tree.
    cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_effects_requirement_payload_total_from_derivation
        _ _ _ selected Hselected)
      as [name_tree [effects Heffects]].
    exists (Phase1GenericEffectsEffectsRequirement name_tree effects).
    rewrite Heffects.
    reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
Qed.

Theorem
  phase1_surface_normalize_generic_requirement_effects_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_generic_requirement_effects_tree tree =
        Some refined /\
      phase1_surface_generic_requirement_effects_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_generic_requirement_proposition_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_generic_requirement_effects_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_generic_requirement_effects_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_generic_requirement_effects_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_effects_tree_round_trip.
    exact Hnormalize.
Qed.
