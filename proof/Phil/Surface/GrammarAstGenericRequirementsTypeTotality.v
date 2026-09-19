From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsTypeSpine
  GrammarAstGenericRequirementTypeTotality
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the generic-requirements type lift from #1207. *)

Lemma phase1_surface_generic_requirement_item_at_tag :
  forall tag,
    nth_error phase1_surface_generic_requirement_items_for_totality
      (phase1_surface_generic_requirement_tag_index tag) =
    Some (phase1_surface_generic_requirement_expression_for_totality tag).
Proof.
  intros tag.
  destruct tag; reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirement_type_spine_total_from_spine_derivation :
  forall requirement path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest (phase1_surface_generic_requirement_spine_tree requirement) ->
    exists refined,
      phase1_surface_normalize_generic_requirement_type_spine requirement =
        Some refined.
Proof.
  intros [tag selected] path input rest Hderive.
  unfold phase1_surface_generic_requirement_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_requirement"
      input rest
      (PTNonterminal "generic_requirement"
        (PTAlternative
          (phase1_surface_generic_requirement_tag_index tag)
          selected))
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
      (PTAlternative
        (phase1_surface_generic_requirement_tag_index tag)
        selected)
      Hbody)
    as [index [item [branch [Hnth [Hbranch Hselected]]]]].
  inversion Hbranch; subst index branch.
  rewrite phase1_surface_generic_requirement_item_at_tag in Hnth.
  inversion Hnth; subst item.
  destruct tag; cbn in Hselected |- *.
  - exists (Phase1GenericStructuralRequirement selected).
    reflexivity.
  - exists (Phase1GenericPropositionRequirement selected).
    reflexivity.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type_total_from_derivation
        "provider" _ _ _ selected Hselected)
      as [name_tree [type_value Htyped]].
    exists (Phase1GenericProviderRequirement name_tree type_value).
    rewrite Htyped.
    reflexivity.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type_total_from_derivation
        "callable" _ _ _ selected Hselected)
      as [name_tree [type_value Htyped]].
    exists (Phase1GenericCallableRequirement name_tree type_value).
    rewrite Htyped.
    reflexivity.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type_total_from_derivation
        "boundary" _ _ _ selected Hselected)
      as [name_tree [type_value Htyped]].
    exists (Phase1GenericBoundaryRequirement name_tree type_value).
    rewrite Htyped.
    reflexivity.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type_total_from_derivation
        "architecture" _ _ _ selected Hselected)
      as [name_tree [type_value Htyped]].
    exists (Phase1GenericArchitectureRequirement name_tree type_value).
    rewrite Htyped.
    reflexivity.
  - exists (Phase1GenericEffectsRequirement selected).
    reflexivity.
  - destruct
      (phase1_surface_normalize_type_only_requirement_type_total_from_derivation
        "authority" _ _ _ selected Hselected)
      as [type_value Htyped].
    exists (Phase1GenericAuthorityRequirement type_value).
    rewrite Htyped.
    reflexivity.
  - destruct
      (phase1_surface_normalize_boundary_representation_requirement_type_total_from_derivation
        _ _ _ selected Hselected)
      as [type_value Htyped].
    exists (Phase1GenericBoundaryRepresentationRequirement type_value).
    rewrite Htyped.
    reflexivity.
  - exists (Phase1GenericRepresentationRequirement selected).
    reflexivity.
  - exists (Phase1GenericPlacementRequirement selected).
    reflexivity.
  - exists (Phase1GenericCostRequirement selected).
    reflexivity.
  - exists (Phase1GenericEnvironmentRequirement selected).
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirement_type_values_total_from_spine_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ENonterminal "generic_requirement" ->
    forall requirements,
      trees = map phase1_surface_generic_requirement_spine_tree requirements ->
      exists refined,
        phase1_surface_normalize_generic_requirement_type_values requirements =
          Some refined.
Proof.
  intros path body input rest trees Hderive Hbody_shape.
  subst body.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros requirements Htrees.
  - destruct requirements as [|requirement requirements]; cbn in Htrees.
    + exists [].
      reflexivity.
    + discriminate Htrees.
  - destruct requirements as [|requirement requirements]; cbn in Htrees;
      try discriminate Htrees.
    inversion Htrees; subst tree trees.
    destruct
      (phase1_surface_normalize_generic_requirement_type_spine_total_from_spine_derivation
        requirement
        (descend path AtRepetitionBody)
        input middle Hitem)
      as [refined Hrefined].
    destruct (IHrest requirements eq_refl)
      as [refined_rest Hrefined_rest].
    exists (refined :: refined_rest).
    cbn.
    rewrite Hrefined, Hrefined_rest.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirements_type_spine_total_from_spine_derivation :
  forall requirements path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_requirements")
      input rest (phase1_surface_generic_requirements_spine_tree requirements) ->
    exists refined,
      phase1_surface_normalize_generic_requirements_type_spine requirements =
        Some refined.
Proof.
  intros [entries] path input rest Hderive.
  unfold phase1_surface_generic_requirements_spine_tree in Hderive.
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
              (map phase1_surface_generic_requirement_spine_tree entries);
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
            (map phase1_surface_generic_requirement_spine_tree entries);
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
  | Hrepeat : Derives phase1_surface_rules _
      (ERepetition (ENonterminal "generic_requirement"))
      _ _
      (PTRepetition
        (map phase1_surface_generic_requirement_spine_tree entries)) |- _ =>
      destruct
        (phase1_surface_repetition_derivation_exposes
          _
          (ENonterminal "generic_requirement")
          _ _
          (PTRepetition
            (map phase1_surface_generic_requirement_spine_tree entries))
          Hrepeat)
        as [entry_trees [Hentry_tree Hentry_body]];
      inversion Hentry_tree; subst entry_trees;
      destruct
        (phase1_surface_normalize_generic_requirement_type_values_total_from_spine_repetition
          _
          (ENonterminal "generic_requirement")
          _ _
          (map phase1_surface_generic_requirement_spine_tree entries)
          Hentry_body eq_refl
          entries eq_refl)
        as [refined_entries Hrefined_entries];
      exists
        {| phase1_generic_requirements_type_spine_entries := refined_entries |};
      cbn;
      rewrite Hrefined_entries;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_generic_requirements_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirements")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_generic_requirements_type_tree tree =
        Some refined /\
      phase1_surface_generic_requirements_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_generic_requirements_spine_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_generic_requirements_type_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_generic_requirements_type_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_generic_requirements_type_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_generic_requirements_type_tree_round_trip.
    exact Hnormalize.
Qed.

Theorem
  phase1_surface_normalize_optional_generic_requirements_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_requirements"))
      input rest tree ->
    exists refined,
      phase1_surface_normalize_optional_generic_requirements_type_tree tree =
        Some refined /\
      phase1_surface_optional_generic_requirements_type_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "generic_requirements")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_generic_requirements_type_tree tree =
        Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_generic_requirements_type_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_generic_requirements_spine_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [base [Hbase Hbase_round_trip]].
    destruct
      (phase1_surface_normalize_generic_requirements_type_tree_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [refined [Hrefined_tree Hrefined_round_trip]].
    assert (Hrefined :
      phase1_surface_normalize_generic_requirements_type_spine base =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirements_type_tree
        in Hrefined_tree.
      rewrite Hbase in Hrefined_tree.
      exact Hrefined_tree.
    }
    assert (Hnormalize :
      phase1_surface_normalize_optional_generic_requirements_type_tree tree =
        Some (Some refined)).
    {
      rewrite Hsome.
      unfold
        phase1_surface_normalize_optional_generic_requirements_type_tree,
        phase1_surface_normalize_optional_generic_requirements,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hbase.
      cbn.
      rewrite Hrefined.
      reflexivity.
    }
    exists (Some refined).
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_generic_requirements_type_tree_round_trip.
      exact Hnormalize.
Qed.
