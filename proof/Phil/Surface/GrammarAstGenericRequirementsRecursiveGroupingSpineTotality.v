From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsPropositionSpine
  GrammarAstGenericRequirementPropositionSpine
  GrammarAstGenericRequirementRecursiveGroupingSpine
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSourceHeader
  GrammarAstSourceHeaderTotality
  GrammarAstGenericRequirementsSpine
  GrammarAstGenericRequirementsTotality
  GrammarDerivation
  GrammarAstGenericRequirementsRecursiveGroupingSpine
  GrammarAstGenericRequirementRecursiveGroupingSpineTotality
  GrammarAstGenericRequirementsPropositionTotality.

Import ListNotations.
Open Scope string_scope.

(* Canonical-Derives converse for the list/optional recursive-grouping lift.
   No child-success or caller-supplied-fuel assumptions. *)

Lemma
  phase1_surface_normalize_generic_requirement_recursive_grouping_values_total_from_spine_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ENonterminal "generic_requirement" ->
    forall requirements,
      trees =
        map phase1_surface_generic_requirement_proposition_spine_tree requirements ->
      exists refined,
        phase1_surface_normalize_generic_requirement_recursive_grouping_values
          requirements = Some refined.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros Hbody_shape requirements Htrees.
  - destruct requirements as [|requirement requirements]; cbn in Htrees.
    + exists [].
      reflexivity.
    + discriminate Htrees.
  - subst body.
    destruct requirements as [|requirement requirements]; cbn in Htrees;
      try discriminate Htrees.
    inversion Htrees; subst tree trees.
    destruct
      (phase1_surface_normalize_generic_requirement_recursive_grouping_spine_total_from_spine_derivation
        requirement
        (descend path AtRepetitionBody)
        input middle Hitem)
      as [refined Hrefined].
    destruct (IHrest eq_refl requirements eq_refl)
      as [refined_rest Hrefined_rest].
    exists (refined :: refined_rest).
    cbn.
    rewrite Hrefined, Hrefined_rest.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirements_recursive_grouping_spine_total_from_spine_derivation :
  forall requirements path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_requirements")
      input rest
      (phase1_surface_generic_requirements_proposition_spine_tree requirements) ->
    exists refined,
      phase1_surface_normalize_generic_requirements_recursive_grouping_spine
        requirements = Some refined.
Proof.
  intros [entries] path input rest Hderive.
  unfold phase1_surface_generic_requirements_proposition_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_requirements"
      input rest
      (PTNonterminal "generic_requirements"
        (PTSequence
          [ PTLiteral "requires";
            PTLiteral "{";
            PTRepetition
              (map phase1_surface_generic_requirement_proposition_spine_tree entries);
            PTLiteral "}"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_requirements_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirements"))
      [ ELiteral "requires";
        ELiteral "{";
        ERepetition (ENonterminal "generic_requirement");
        ELiteral "}"
      ]
      input rest
      (PTSequence
        [ PTLiteral "requires";
          PTLiteral "{";
          PTRepetition
            (map phase1_surface_generic_requirement_proposition_spine_tree entries);
          PTLiteral "}"
        ])
      Hbody)
    as [trees [Hsequence_tree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirements")) 0
      (ELiteral "requires")
      [ ELiteral "{";
        ERepetition (ENonterminal "generic_requirement");
        ELiteral "}" ]
      input rest trees Hitems)
    as [after_requires [requires_tree [tail1_trees
      [Htrees [Hrequires Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirements")) 1
      (ELiteral "{")
      [ ERepetition (ENonterminal "generic_requirement");
        ELiteral "}" ]
      after_requires rest tail1_trees Htail1)
    as [after_open [open_tree [tail2_trees
      [Htail1_trees [Hopen Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirements")) 2
      (ERepetition (ENonterminal "generic_requirement"))
      [ ELiteral "}" ]
      after_open rest tail2_trees Htail2)
    as [after_entries [entries_tree [tail3_trees
      [Htail2_trees [Hentries Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirements")) 3
      (ELiteral "}") []
      after_entries rest tail3_trees Htail3)
    as [after_close [close_tree [nil_trees
      [Htail3_trees [Hclose Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees
    in Hsequence_tree.
  inversion Hnil; subst nil_trees.
  inversion Hsequence_tree; subst.
  destruct
    (phase1_surface_repetition_derivation_exposes
      _ (ENonterminal "generic_requirement")
      _ _ (PTRepetition (map phase1_surface_generic_requirement_proposition_spine_tree entries))
      Hentries)
    as [entry_trees [Hentry_tree Hentry_body]].
  inversion Hentry_tree; subst entry_trees.
  destruct
    (phase1_surface_normalize_generic_requirement_recursive_grouping_values_total_from_spine_repetition
      _
      (ENonterminal "generic_requirement")
      _ _
      (map phase1_surface_generic_requirement_proposition_spine_tree entries)
      Hentry_body eq_refl entries eq_refl)
    as [refined_entries Hrefined_entries].
  exists {| phase1_generic_requirements_recursive_grouping_spine_entries := refined_entries |}.
  unfold phase1_surface_normalize_generic_requirements_recursive_grouping_spine.
  cbn [phase1_generic_requirements_proposition_spine_entries].
  rewrite Hrefined_entries.
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_generic_requirements_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirements")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_generic_requirements_recursive_grouping_tree tree =
        Some refined /\
      phase1_surface_generic_requirements_recursive_grouping_spine_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_generic_requirements_proposition_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_generic_requirements_recursive_grouping_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_generic_requirements_recursive_grouping_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_generic_requirements_recursive_grouping_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirements_recursive_grouping_tree_round_trip.
    exact Hnormalize.
Qed.

Theorem
  phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_requirements"))
      input rest tree ->
    exists refined,
      phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree
        tree = Some refined /\
      phase1_surface_optional_generic_requirements_recursive_grouping_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "generic_requirements")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree
        tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_generic_requirements_proposition_tree_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [base [Hbase Hbase_round_trip]].
    destruct
      (phase1_surface_normalize_generic_requirements_recursive_grouping_tree_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [refined [Hrefined_tree Hrefined_round_trip]].
    assert (Hrefined :
      phase1_surface_normalize_generic_requirements_recursive_grouping_spine base =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirements_recursive_grouping_tree
        in Hrefined_tree.
      rewrite Hbase in Hrefined_tree.
      exact Hrefined_tree.
    }
    assert (Hbase_optional :
      phase1_surface_normalize_optional_generic_requirements_proposition_tree tree =
        Some (Some base)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_generic_requirements_proposition_tree,
        phase1_surface_normalize_optional_generic_requirements_type_tree,
        phase1_surface_normalize_optional_generic_requirements,
        phase1_surface_expect_optional.
      cbn [phase1_surface_expect_optional].
      unfold phase1_surface_normalize_generic_requirements_proposition_tree,
        phase1_surface_normalize_generic_requirements_type_tree in Hbase.
      destruct (phase1_surface_normalize_generic_requirements_spine body)
        as [raw |] eqn:Hraw; simpl in Hbase; try discriminate Hbase.
      destruct (phase1_surface_normalize_generic_requirements_type_spine raw)
        as [typed |] eqn:Htyped; simpl in Hbase; try discriminate Hbase.
      cbn [phase1_surface_normalize_optional_generic_requirements_type
           phase1_surface_normalize_optional_generic_requirements_proposition].
      rewrite Hbase.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree
        tree = Some (Some refined)).
    {
      unfold
        phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree.
      rewrite Hbase_optional.
      cbn.
      rewrite Hrefined.
      reflexivity.
    }
    exists (Some refined).
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree_round_trip.
      exact Hnormalize.
Qed.
