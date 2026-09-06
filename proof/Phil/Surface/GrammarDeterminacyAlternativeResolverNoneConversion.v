From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyRelationCommitmentSoundness
  GrammarDeterminacyPredictiveFallbackSoundness
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyAlternativeResolverContext
  GrammarDeterminacyAlternativeEarlierDisjoint
  GrammarDeterminacyAlternativeResolverNoneSemantic
  GrammarDeterminacyStaticValueResolverNoneFallback
  GrammarDeterminacyPredictiveConversion.

Import ListNotations.
Open Scope string_scope.

(*
  Unified certified-resolver-None conversion for alternative resolver roots.

  The assembly classifier identifies exactly six generated alternative roots
  whose FIRST overlap is handled by the certified resolver.  #756 proved that
  every selected branch at those roots is either FIRST-disjoint from all
  earlier branches or belongs to a small finite exception set.  #760 ruled out
  the resolver-backed semantic exceptions when the resolver returns None, and
  #762 closed the one input-sensitive residue: static_argument branch 2.

  This file composes those pieces into the theorem consumed directly by the
  final ordinary-derivation -> predictive-oracle induction.
*)

Lemma resolver_none_nat_memb_true_in :
  forall needle haystack,
    nat_memb needle haystack = true ->
    In needle haystack.
Proof.
  intros needle haystack Hmem.
  unfold nat_memb in Hmem.
  apply existsb_exists in Hmem.
  destruct Hmem as [candidate [Hin Heq]].
  apply Nat.eqb_eq in Heq.
  subst candidate.
  exact Hin.
Qed.

Lemma selected_earlier_first_disjointb_oracle_alternative :
  forall path items index item input rest tree,
    phase1_surface_certified_overlap_resolver path input = None ->
    phase1_surface_expression_path_context path (EAlternative items) ->
    selected_earlier_first_disjointb items index = true ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index))
      item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input =
      Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree
    Hresolver Hpath Hdisjoint Hnth Hderive Hsafe Hnonnullable.
  eapply predictive_bridge_oracle_from_fallback.
  - exact Hresolver.
  - exact Hpath.
  - eapply predictive_fallback_alternative_from_derivation.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + intros earlier_index earlier_item Hlt Hearlier.
      eapply selected_earlier_first_disjointb_excludes_earlier_alternative.
      * exact Hdisjoint.
      * exact Hnth.
      * exact Hderive.
      * exact Hsafe.
      * exact Hnonnullable.
      * exact Hlt.
      * exact Hearlier.
Qed.

Lemma phase1_surface_declaration_resolver_none_oracle_alternative :
  forall path items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path provider_declaration_suffix = true ->
    lookupRule "declaration" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = None ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  unfold provider_declaration_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "declaration" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_declaration_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  destruct
    (alternative_exception_coverage_selected
      phase1_surface_resolver_declaration_items
      declaration_resolver_exception_indices
      index item
      phase1_surface_declaration_resolver_exception_coverage Hnth)
    as [Hexception | Hdisjoint].
  - apply resolver_none_nat_memb_true_in in Hexception.
    unfold declaration_resolver_exception_indices in Hexception.
    simpl in Hexception.
    destruct Hexception as [Hindex | [Hindex | Hfalse]].
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_provider_contract_resolver_none_impossible.
      * exact Hderive.
      * exact Hresolver.
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_provider_implementation_resolver_none_impossible.
      * exact Hderive.
      * exact Hresolver.
    + contradiction.
  - eapply selected_earlier_first_disjointb_oracle_alternative; eauto.
Qed.

Lemma phase1_surface_generic_requirement_resolver_none_oracle_alternative :
  forall path items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path generic_requirement_suffix = true ->
    lookupRule "generic_requirement" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = None ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  unfold generic_requirement_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "generic_requirement" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_generic_requirement_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  destruct
    (alternative_exception_coverage_selected
      phase1_surface_resolver_generic_requirement_items
      generic_requirement_resolver_exception_indices
      index item
      phase1_surface_generic_requirement_resolver_exception_coverage Hnth)
    as [Hexception | Hdisjoint].
  - apply resolver_none_nat_memb_true_in in Hexception.
    unfold generic_requirement_resolver_exception_indices in Hexception.
    simpl in Hexception.
    destruct Hexception as [Hindex | [Hindex | Hfalse]].
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_generic_boundary_name_resolver_none_impossible.
      * exact Hderive.
      * exact Hresolver.
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_generic_boundary_representation_resolver_none_impossible.
      * exact Hderive.
      * exact Hresolver.
    + contradiction.
  - eapply selected_earlier_first_disjointb_oracle_alternative; eauto.
Qed.

Lemma phase1_surface_pattern_resolver_none_oracle_alternative :
  forall path items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path pattern_suffix = true ->
    lookupRule "pattern" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = None ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  unfold pattern_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "pattern" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_pattern_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  destruct
    (alternative_exception_coverage_selected
      phase1_surface_resolver_pattern_items
      pattern_resolver_exception_indices
      index item
      phase1_surface_pattern_resolver_exception_coverage Hnth)
    as [Hexception | Hdisjoint].
  - apply resolver_none_nat_memb_true_in in Hexception.
    unfold pattern_resolver_exception_indices in Hexception.
    simpl in Hexception.
    destruct Hexception as [Hindex | Hfalse].
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_record_pattern_resolver_none_impossible.
      * exact Hderive.
      * exact Hresolver.
    + contradiction.
  - eapply selected_earlier_first_disjointb_oracle_alternative; eauto.
Qed.

Lemma phase1_surface_primary_expression_resolver_none_oracle_alternative :
  forall path items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path primary_expression_suffix = true ->
    lookupRule "primary_expression" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = None ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  unfold primary_expression_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "primary_expression" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_primary_expression_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  destruct
    (alternative_exception_coverage_selected
      phase1_surface_resolver_primary_expression_items
      primary_expression_resolver_exception_indices
      index item
      phase1_surface_primary_expression_resolver_exception_coverage Hnth)
    as [Hexception | Hdisjoint].
  - apply resolver_none_nat_memb_true_in in Hexception.
    unfold primary_expression_resolver_exception_indices in Hexception.
    simpl in Hexception.
    destruct Hexception as [Hindex | Hfalse].
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_parenthesized_expression_resolver_none_impossible.
      * exact Hderive.
      * exact Hresolver.
    + contradiction.
  - eapply selected_earlier_first_disjointb_oracle_alternative; eauto.
Qed.

Lemma phase1_surface_proposition_atom_resolver_none_oracle_alternative :
  forall path outer_follow items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path proposition_atom_suffix = true ->
    lookupRule "proposition_atom" phase1_surface_rules = Some (EAlternative items) ->
    outer_follow = lookup_tokens "proposition_atom" phase1_surface_follow_facts ->
    phase1_surface_certified_overlap_resolver path input = None ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path outer_follow items index item input rest tree
    Hpath Hsuffix Hlookup Hfollow Hresolver Hnth Hderive Hsafe Hnonnullable
    Hcontinuation.
  unfold proposition_atom_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "proposition_atom" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_proposition_atom_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  assert (Hproposition_continuation :
    continuation_lookahead_mem rest phase1_surface_proposition_atom_follow = true).
  {
    Transparent phase1_surface_proposition_atom_follow.
    unfold phase1_surface_proposition_atom_follow.
    rewrite <- Hfollow.
    exact Hcontinuation.
  }
  destruct
    (alternative_exception_coverage_selected
      phase1_surface_resolver_proposition_atom_items
      proposition_atom_resolver_exception_indices
      index item
      phase1_surface_proposition_atom_resolver_exception_coverage Hnth)
    as [Hexception | Hdisjoint].
  - apply resolver_none_nat_memb_true_in in Hexception.
    unfold proposition_atom_resolver_exception_indices in Hexception.
    simpl in Hexception.
    destruct Hexception as
      [Hindex | [Hindex | [Hindex | [Hindex | Hfalse]]]].
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_grouped_proposition_resolver_none_impossible.
      * exact Hderive.
      * exact Hproposition_continuation.
      * exact Hresolver.
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_true_proposition_resolver_none_impossible.
      * exact Hderive.
      * exact Hproposition_continuation.
      * exact Hresolver.
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_false_proposition_resolver_none_impossible.
      * exact Hderive.
      * exact Hproposition_continuation.
      * exact Hresolver.
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_claim_application_resolver_none_impossible.
      * exact Hderive.
      * exact Hproposition_continuation.
      * exact Hresolver.
    + contradiction.
  - eapply selected_earlier_first_disjointb_oracle_alternative; eauto.
Qed.

Lemma phase1_surface_static_argument_resolver_none_oracle_alternative :
  forall path items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path static_argument_suffix = true ->
    lookupRule "static_argument" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = None ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  pose proof Hsuffix as Hsuffix_original.
  unfold static_argument_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "static_argument" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_static_argument_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  destruct
    (alternative_exception_coverage_selected
      phase1_surface_resolver_static_argument_items
      static_argument_resolver_exception_indices
      index item
      phase1_surface_static_argument_resolver_exception_coverage Hnth)
    as [Hexception | Hdisjoint].
  - apply resolver_none_nat_memb_true_in in Hexception.
    unfold static_argument_resolver_exception_indices in Hexception.
    simpl in Hexception.
    destruct Hexception as [Hindex | [Hindex | Hfalse]].
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      eapply phase1_surface_static_value_resolver_none_oracle.
      * exact Hpath.
      * exact Hsuffix_original.
      * exact phase1_surface_resolver_static_argument_lookup_exact.
      * exact Hresolver.
      * exact Hderive.
    + subst index.
      vm_compute in Hnth.
      inversion Hnth; subst item.
      exfalso.
      eapply phase1_surface_effect_set_resolver_none_impossible.
      * exact Hderive.
      * exact Hresolver.
    + contradiction.
  - eapply selected_earlier_first_disjointb_oracle_alternative; eauto.
Qed.

Theorem phase1_surface_resolver_none_oracle_alternative :
  forall path outer_follow items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    alternative_resolver_contextb path outer_follow = true ->
    phase1_surface_certified_overlap_resolver path input = None ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path outer_follow items index item input rest tree
    Hpath Hresolver_context Hresolver Hnth Hderive Hsafe Hnonnullable
    Hcontinuation.
  pose proof
    (phase1_surface_alternative_resolver_root_classified
      path outer_follow items Hpath Hresolver_context)
    as Hroot.
  destruct Hroot as
    [Hsuffix Hlookup
    | Hsuffix Hlookup
    | Hsuffix Hlookup Hfollow
    | Hsuffix Hlookup
    | Hsuffix Hlookup Hfollow
    | Hsuffix Hlookup].
  - eapply phase1_surface_declaration_resolver_none_oracle_alternative; eauto.
  - eapply phase1_surface_generic_requirement_resolver_none_oracle_alternative; eauto.
  - eapply phase1_surface_pattern_resolver_none_oracle_alternative; eauto.
  - eapply phase1_surface_primary_expression_resolver_none_oracle_alternative; eauto.
  - eapply phase1_surface_proposition_atom_resolver_none_oracle_alternative; eauto.
  - eapply phase1_surface_static_argument_resolver_none_oracle_alternative; eauto.
Qed.
