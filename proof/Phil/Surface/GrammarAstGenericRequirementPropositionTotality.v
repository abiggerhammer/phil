From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementPropositionSpine
  GrammarAstGenericRequirementTypeTotality
  GrammarAstPropositionTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the generic-requirement proposition refinement from #1216. *)

Definition phase1_surface_generic_requirement_type_tag
  (requirement : Phase1SurfaceGenericRequirementTypeSpine)
  : Phase1SurfaceGenericRequirementTag :=
  match requirement with
  | Phase1GenericStructuralRequirement _ =>
      Phase1StructuralRequirement
  | Phase1GenericPropositionRequirement _ =>
      Phase1PropositionRequirement
  | Phase1GenericProviderRequirement _ _ =>
      Phase1ProviderRequirement
  | Phase1GenericCallableRequirement _ _ =>
      Phase1CallableRequirement
  | Phase1GenericBoundaryRequirement _ _ =>
      Phase1BoundaryRequirement
  | Phase1GenericArchitectureRequirement _ _ =>
      Phase1ArchitectureRequirement
  | Phase1GenericEffectsRequirement _ =>
      Phase1EffectsRequirement
  | Phase1GenericAuthorityRequirement _ =>
      Phase1AuthorityRequirement
  | Phase1GenericBoundaryRepresentationRequirement _ =>
      Phase1BoundaryRepresentationRequirement
  | Phase1GenericRepresentationRequirement _ =>
      Phase1RepresentationRequirement
  | Phase1GenericPlacementRequirement _ =>
      Phase1PlacementRequirement
  | Phase1GenericCostRequirement _ =>
      Phase1CostRequirement
  | Phase1GenericEnvironmentRequirement _ =>
      Phase1EnvironmentRequirement
  end.

Lemma phase1_surface_generic_requirement_type_item :
  forall requirement,
    nth_error phase1_surface_generic_requirement_items_for_totality
      (phase1_surface_generic_requirement_type_spine_index requirement) =
    Some
      (phase1_surface_generic_requirement_expression_for_totality
        (phase1_surface_generic_requirement_type_tag requirement)).
Proof.
  intros requirement.
  destruct requirement; reflexivity.
Qed.

Lemma phase1_surface_generic_requirement_type_selected_derivation :
  forall requirement path input rest,
    Derives phase1_surface_rules path
      (ENonterminal "generic_requirement")
      input rest
      (phase1_surface_generic_requirement_type_spine_tree requirement) ->
    Derives phase1_surface_rules
      (descend
        (descend path (AtNonterminal "generic_requirement"))
        (AtAlternative
          (phase1_surface_generic_requirement_type_spine_index requirement)))
      (phase1_surface_generic_requirement_expression_for_totality
        (phase1_surface_generic_requirement_type_tag requirement))
      input rest
      (phase1_surface_generic_requirement_type_selected_tree requirement).
Proof.
  intros requirement path input rest Hderive.
  unfold phase1_surface_generic_requirement_type_spine_tree in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_requirement"
      input rest
      (PTNonterminal "generic_requirement"
        (PTAlternative
          (phase1_surface_generic_requirement_type_spine_index requirement)
          (phase1_surface_generic_requirement_type_selected_tree requirement)))
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
        (phase1_surface_generic_requirement_type_spine_index requirement)
        (phase1_surface_generic_requirement_type_selected_tree requirement))
      Hbody)
    as [index [item [selected [Hnth [Hselected_tree Hselected]]]]].
  inversion Hselected_tree; subst index selected.
  rewrite phase1_surface_generic_requirement_type_item in Hnth.
  inversion Hnth; subst item.
  exact Hselected.
Qed.

Lemma
  phase1_surface_normalize_proposition_requirement_payload_total_from_derivation :
  forall keyword path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral keyword;
          ENonterminal "proposition";
          ELiteral ";"
        ])
      input rest tree ->
    exists proposition,
      phase1_surface_normalize_proposition_requirement_payload keyword tree =
        Some proposition.
Proof.
  intros keyword path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral keyword;
        ENonterminal "proposition";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral keyword)
      [ ENonterminal "proposition";
        ELiteral ";" ]
      input rest trees Hitems)
    as [after_keyword [keyword_tree [tail1
      [Htrees [Hkeyword Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "proposition")
      [ ELiteral ";" ]
      after_keyword rest tail1 Htail1)
    as [after_proposition [proposition_tree [tail2
      [Htail1_trees [Hproposition Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (ELiteral ";") []
      after_proposition rest tail2 Htail2)
    as [after_terminator [terminator_tree [nil_trees
      [Htail2_trees [Hterminator Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
    as [keyword_tail [_ [_ Hkeyword_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
    as [terminator_tail [_ [_ Hterminator_tree]]].
  destruct
    (phase1_surface_normalize_proposition_spine_total_from_derivation
      _ _ _ proposition_tree Hproposition)
    as [proposition [Hproposition_normalize Hproposition_round_trip]].
  exists proposition.
  rewrite Htree, Hkeyword_tree, Hterminator_tree.
  unfold phase1_surface_normalize_proposition_requirement_payload,
    phase1_surface_expect_sequence,
    phase1_surface_exact3,
    phase1_surface_expect_literal.
  cbn.
  rewrite String.eqb_refl.
  rewrite Hproposition_normalize.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_generic_requirement_proposition_spine_total_from_spine_derivation :
  forall requirement path input rest,
    Derives phase1_surface_rules path
      (ENonterminal "generic_requirement")
      input rest
      (phase1_surface_generic_requirement_type_spine_tree requirement) ->
    exists refined,
      phase1_surface_normalize_generic_requirement_proposition_spine requirement =
        Some refined.
Proof.
  intros requirement path input rest Hderive.
  pose proof
    (phase1_surface_generic_requirement_type_selected_derivation
      requirement path input rest Hderive) as Hselected.
  destruct requirement; cbn in Hselected |- *.
  - eexists. reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload_total_from_derivation
        "proposition" _ _ _ selected Hselected)
      as [proposition Hproposition].
    exists (Phase1GenericPropositionPropositionRequirement proposition).
    rewrite Hproposition.
    reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload_total_from_derivation
        "representation" _ _ _ selected Hselected)
      as [proposition Hproposition].
    exists (Phase1GenericRepresentationPropositionRequirement proposition).
    rewrite Hproposition.
    reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload_total_from_derivation
        "placement" _ _ _ selected Hselected)
      as [proposition Hproposition].
    exists (Phase1GenericPlacementPropositionRequirement proposition).
    rewrite Hproposition.
    reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload_total_from_derivation
        "cost" _ _ _ selected Hselected)
      as [proposition Hproposition].
    exists (Phase1GenericCostPropositionRequirement proposition).
    rewrite Hproposition.
    reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload_total_from_derivation
        "environment" _ _ _ selected Hselected)
      as [proposition Hproposition].
    exists (Phase1GenericEnvironmentPropositionRequirement proposition).
    rewrite Hproposition.
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_generic_requirement_proposition_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_generic_requirement_proposition_tree tree =
        Some refined /\
      phase1_surface_generic_requirement_proposition_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_generic_requirement_type_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_generic_requirement_proposition_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_generic_requirement_proposition_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_generic_requirement_proposition_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_proposition_tree_round_trip.
    exact Hnormalize.
Qed.
