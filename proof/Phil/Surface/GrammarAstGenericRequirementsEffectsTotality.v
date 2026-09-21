From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsEffectsSpine
  GrammarAstGenericRequirementEffectsTotality
  GrammarAstGenericRequirementsPropositionTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the generic-requirements effects lift from #1262. *)

Lemma
  phase1_surface_normalize_generic_requirement_effects_values_total_from_spine_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ENonterminal "generic_requirement" ->
    forall requirements,
      trees =
        map
          phase1_surface_generic_requirement_proposition_spine_tree
          requirements ->
      exists refined,
        phase1_surface_normalize_generic_requirement_effects_values
          requirements = Some refined.
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
      (phase1_surface_normalize_generic_requirement_effects_spine_total_from_spine_derivation
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
  phase1_surface_normalize_generic_requirements_effects_spine_total_from_spine_derivation :
  forall requirements path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_requirements")
      input rest
      (phase1_surface_generic_requirements_proposition_spine_tree requirements) ->
    exists refined,
      phase1_surface_normalize_generic_requirements_effects_spine requirements =
        Some refined.
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
              (map
                phase1_surface_generic_requirement_proposition_spine_tree
                entries);
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
            (map
              phase1_surface_generic_requirement_proposition_spine_tree
              entries);
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
        (map
          phase1_surface_generic_requirement_proposition_spine_tree
          entries)) |- _ =>
      destruct
        (phase1_surface_repetition_derivation_exposes
          _
          (ENonterminal "generic_requirement")
          _ _
          (PTRepetition
            (map
              phase1_surface_generic_requirement_proposition_spine_tree
              entries))
          Hrepeat)
        as [entry_trees [Hentry_tree Hentry_body]];
      inversion Hentry_tree; subst entry_trees;
      destruct
        (phase1_surface_normalize_generic_requirement_effects_values_total_from_spine_repetition
          _
          (ENonterminal "generic_requirement")
          _ _
          (map
            phase1_surface_generic_requirement_proposition_spine_tree
            entries)
          Hentry_body eq_refl
          entries eq_refl)
        as [refined_entries Hrefined_entries];
      exists
        {| phase1_generic_requirements_effects_spine_entries :=
             refined_entries |};
      cbn;
      rewrite Hrefined_entries;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_generic_requirements_effects_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirements")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_generic_requirements_effects_tree tree =
        Some refined /\
      phase1_surface_generic_requirements_effects_spine_tree refined =
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
    (phase1_surface_normalize_generic_requirements_effects_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_generic_requirements_effects_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_generic_requirements_effects_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirements_effects_tree_round_trip.
    exact Hnormalize.
Qed.

Theorem
  phase1_surface_normalize_optional_generic_requirements_effects_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_requirements"))
      input rest tree ->
    exists refined,
      phase1_surface_normalize_optional_generic_requirements_effects_tree tree =
        Some refined /\
      phase1_surface_optional_generic_requirements_effects_tree refined =
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
      phase1_surface_normalize_optional_generic_requirements_effects_tree tree =
        Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_generic_requirements_effects_tree_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_generic_requirements_proposition_tree_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [base [Hbase Hbase_round_trip]].
    destruct
      (phase1_surface_normalize_generic_requirements_effects_tree_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [refined [Hrefined_tree Hrefined_round_trip]].
    assert (Hrefined :
      phase1_surface_normalize_generic_requirements_effects_spine base =
        Some refined).
    {
      unfold phase1_surface_normalize_generic_requirements_effects_tree
        in Hrefined_tree.
      rewrite Hbase in Hrefined_tree.
      exact Hrefined_tree.
    }
    assert (Hbase_optional :
      phase1_surface_normalize_optional_generic_requirements_proposition_tree
        tree = Some (Some base)).
    {
      rewrite Hsome.
      unfold
        phase1_surface_normalize_optional_generic_requirements_proposition_tree.
      destruct
        (phase1_surface_normalize_optional_generic_requirements_type_tree
          (PTOptionalSome body))
        as [requirements |] eqn:Htype_optional.
      - cbn.
        destruct requirements as [requirements |].
        + destruct
            (phase1_surface_normalize_generic_requirements_proposition_spine
              requirements)
            as [actual |] eqn:Hprop; try discriminate.
          f_equal.
          assert (Hrequirements :
            phase1_surface_normalize_generic_requirements_type_tree body =
              Some requirements).
          {
            unfold
              phase1_surface_normalize_optional_generic_requirements_type_tree
              in Htype_optional.
            rewrite Hsome in Htype_optional.
            cbn in Htype_optional.
            destruct
              (phase1_surface_normalize_generic_requirements_type_tree body)
              as [actual_requirements |] eqn:Hactual;
              try discriminate Htype_optional.
            inversion Htype_optional; subst requirements.
            exact Hactual.
          }
          rewrite Hrequirements in Hbase.
          inversion Hbase.
          exact Hprop.
        + discriminate Htype_optional.
      - exfalso.
        unfold
          phase1_surface_normalize_optional_generic_requirements_type_tree
          in Htype_optional.
        rewrite Hsome in Htype_optional.
        cbn in Htype_optional.
        rewrite
          (proj1
            (phase1_surface_normalize_generic_requirements_proposition_tree_total_from_derivation
              (descend path AtOptionalBody)
              input rest body Hbody)).
        discriminate.
    }
    assert (Hnormalize :
      phase1_surface_normalize_optional_generic_requirements_effects_tree tree =
        Some (Some refined)).
    {
      unfold
        phase1_surface_normalize_optional_generic_requirements_effects_tree.
      rewrite Hbase_optional.
      cbn.
      rewrite Hrefined.
      reflexivity.
    }
    exists (Some refined).
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_generic_requirements_effects_tree_round_trip.
      exact Hnormalize.
Qed.
