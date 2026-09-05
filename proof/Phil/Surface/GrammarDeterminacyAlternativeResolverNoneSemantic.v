From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyPredictiveFallbackSoundness
  GrammarDeterminacyAlternativeEarlierDisjoint
  GrammarDeterminacyAlternativeResolverSemanticCore
  GrammarDeterminacyAlternativeResolverSemanticComplex.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic core for the certified-resolver-None half of the final
  PHIL-SURFACE-DETERM-001 alternative conversion.

  #756 mechanically certified that every selected alternative at the six
  resolver roots either has FIRST disjoint from every earlier alternative or
  belongs to a small overlap-exception set.  The first theorem below turns the
  positive checker result into the exact input rejection fact consumed by
  predictive fallback.  The remaining theorems package the semantic fact that
  an ordinary derivation through a resolver-backed overlap cannot coexist with
  the certified resolver returning None.

  Static-value branch 2 is intentionally only excluded here when its input
  begins with "(".  The branch also has non-overlap starts for which the
  resolver correctly returns None; the successor slice will prove the needed
  input-sensitive earlier-branch exclusion for that residual case.
*)

Lemma selected_earlier_first_disjointb_excludes_earlier_alternative :
  forall path items index item input rest tree,
    selected_earlier_first_disjointb items index = true ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index))
      item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    forall earlier_index earlier_item,
      earlier_index < index ->
      nth_error items earlier_index = Some earlier_item ->
      expression_starts_inputb earlier_item input = false.
Proof.
  intros path items index item input rest tree
    Hselected_disjoint Hnth Hderive Hsafe Hnonnullable
    earlier_index earlier_item Hlt Hearlier.
  pose proof
    (selected_earlier_first_disjointb_sound
      items index item earlier_index earlier_item
      Hselected_disjoint Hnth Hlt Hearlier)
    as Hdisjoint.
  pose proof
    (phase1_surface_nonnullable_derivation_starts_inputb
      (descend path (AtAlternative index))
      item input rest tree Hderive Hsafe Hnonnullable)
    as Hselected.
  destruct input as [| first_token tail].
  - rewrite expression_starts_inputb_nil_equation in Hselected.
    rewrite Hnonnullable in Hselected.
    discriminate Hselected.
  - rewrite expression_starts_inputb_cons_equation in Hselected.
    rewrite expression_starts_inputb_cons_equation.
    eapply token_intersection_empty_excludes_shared_member.
    + exact Hdisjoint.
    + exact Hselected.
Qed.

Lemma certified_overlap_resolver_none_excludes_some :
  forall path input decision,
    phase1_surface_certified_overlap_resolver path input = None ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    False.
Proof.
  intros path input decision Hnone Hsome.
  rewrite Hnone in Hsome.
  discriminate Hsome.
Qed.

Theorem phase1_surface_provider_contract_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "provider_contract_decl") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "declaration")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_provider_contract_certified_commitment.
    exact Hderive.
Qed.

Theorem phase1_surface_provider_implementation_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "provider_implementation_decl") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "declaration")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_provider_implementation_certified_commitment.
    exact Hderive.
Qed.

Theorem phase1_surface_generic_boundary_name_resolver_none_impossible :
  forall root_prefix branch_path tail_items input rest tree,
    Derives phase1_surface_rules branch_path
      (ESequence
        (ELiteral "boundary" ::
         ENonterminal "identifier" ::
         tail_items))
      input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "generic_requirement")) input = None ->
    False.
Proof.
  intros root_prefix branch_path tail_items input rest tree Hderive Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_generic_boundary_name_certified_commitment.
    exact Hderive.
Qed.

Theorem phase1_surface_generic_boundary_representation_resolver_none_impossible :
  forall root_prefix branch_path tail_items input rest tree,
    Derives phase1_surface_rules branch_path
      (ESequence
        (ELiteral "boundary" ::
         ELiteral "representation" ::
         tail_items))
      input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "generic_requirement")) input = None ->
    False.
Proof.
  intros root_prefix branch_path tail_items input rest tree Hderive Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_generic_boundary_representation_certified_commitment.
    exact Hderive.
Qed.

Theorem phase1_surface_record_pattern_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "record_pattern") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "pattern")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_record_pattern_certified_commitment.
    exact Hderive.
Qed.

Theorem phase1_surface_parenthesized_expression_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "parenthesized_expression") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "primary_expression")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_parenthesized_expression_certified_commitment.
    exact Hderive.
Qed.

Theorem phase1_surface_grouped_proposition_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      phase1_surface_grouped_proposition_expression input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_grouped_proposition_certified_commitment.
    + exact Hderive.
    + exact Hcontinuation.
Qed.

Theorem phase1_surface_true_proposition_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ELiteral "true") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_true_proposition_certified_commitment.
    + exact Hderive.
    + exact Hcontinuation.
Qed.

Theorem phase1_surface_false_proposition_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ELiteral "false") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_false_proposition_certified_commitment.
    + exact Hderive.
    + exact Hcontinuation.
Qed.

Theorem phase1_surface_claim_application_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "claim_application") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_claim_application_certified_commitment.
    + exact Hderive.
    + exact Hcontinuation.
Qed.

Theorem phase1_surface_static_value_parenthesis_resolver_none_impossible :
  forall root_prefix branch_path input rest tree tail,
    Derives phase1_surface_rules branch_path
      (ENonterminal "static_value_expression") input rest tree ->
    input = TLiteral "(" :: tail ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "static_argument")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree tail Hderive Hinput Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_static_value_parenthesis_certified_commitment.
    + exact Hderive.
    + exact Hinput.
Qed.

Theorem phase1_surface_effect_set_resolver_none_impossible :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "effect_set_literal") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "static_argument")) input = None ->
    False.
Proof.
  intros root_prefix branch_path input rest tree Hderive Hnone.
  eapply certified_overlap_resolver_none_excludes_some.
  - exact Hnone.
  - eapply phase1_surface_effect_set_certified_commitment.
    exact Hderive.
Qed.
