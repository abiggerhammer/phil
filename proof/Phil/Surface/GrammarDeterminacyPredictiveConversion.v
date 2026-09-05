From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyPredictiveFallbackSoundness
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection
  GrammarDeterminacyPredictiveBridge.

Import ListNotations.

(*
  First executable layer of the final ordinary-derivation -> predictive-oracle
  conversion for PHIL-SURFACE-DETERM-001.

  #733 packaged the structural invariants consumed by the eventual mutual
  induction.  This file turns the fallback half of those invariants into actual
  decisions of phase1_surface_predictive_oracle.  Certified resolver cases are
  deliberately left separate: the final induction can destruct the resolver
  result once, use the semantic resolver theorem when it is Some, and use these
  lemmas when it is None.
*)

Lemma predictive_bridge_oracle_from_fallback :
  forall path expression input decision,
    phase1_surface_certified_overlap_resolver path input = None ->
    phase1_surface_expression_path_context path expression ->
    predictive_fallback_decision expression input = Some decision ->
    phase1_surface_predictive_oracle path input = Some decision.
Proof.
  intros path expression input decision Hresolver Hpath Hfallback.
  unfold phase1_surface_predictive_oracle.
  rewrite Hresolver.
  unfold phase1_surface_expression_path_context in Hpath.
  rewrite Hpath.
  exact Hfallback.
Qed.

Lemma predictive_bridge_oracle_from_resolver :
  forall path input decision,
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    phase1_surface_predictive_oracle path input = Some decision.
Proof.
  intros path input decision Hresolver.
  exact
    (phase1_surface_predictive_oracle_extends_certified_overlap_resolver
      path input decision Hresolver).
Qed.

Lemma predictive_bridge_pairwise_excludes_earlier_alternative :
  forall path items index item input rest tree,
    alternatives_pairwise_first_disjointb items = true ->
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
    Hpairwise Hnth Hderive Hsafe Hnonnullable
    earlier_index earlier_item Hlt Hearlier.
  pose proof
    (alternatives_pairwise_first_disjointb_nth_lt_sound
      items earlier_index earlier_item index item
      Hpairwise Hearlier Hnth Hlt)
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

Lemma predictive_bridge_pairwise_fallback_alternative :
  forall path items index item input rest tree,
    alternatives_pairwise_first_disjointb items = true ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index))
      item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    predictive_fallback_decision (EAlternative items) input =
      Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree
    Hpairwise Hnth Hderive Hsafe Hnonnullable.
  eapply predictive_fallback_alternative_from_derivation.
  - exact Hnth.
  - exact Hderive.
  - exact Hsafe.
  - exact Hnonnullable.
  - intros earlier_index earlier_item Hlt Hearlier.
    exact
      (predictive_bridge_pairwise_excludes_earlier_alternative
        path items index item input rest tree
        Hpairwise Hnth Hderive Hsafe Hnonnullable
        earlier_index earlier_item Hlt Hearlier).
Qed.

Lemma predictive_bridge_pairwise_oracle_alternative :
  forall path items index item input rest tree,
    phase1_surface_certified_overlap_resolver path input = None ->
    phase1_surface_expression_path_context path (EAlternative items) ->
    alternatives_pairwise_first_disjointb items = true ->
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
    Hresolver Hpath Hpairwise Hnth Hderive Hsafe Hnonnullable.
  eapply predictive_bridge_oracle_from_fallback.
  - exact Hresolver.
  - exact Hpath.
  - eapply predictive_bridge_pairwise_fallback_alternative; eauto.
Qed.

Lemma predictive_bridge_optional_present_oracle_fallback :
  forall path body input rest tree,
    phase1_surface_certified_overlap_resolver path input = None ->
    phase1_surface_expression_path_context path (EOptional body) ->
    Derives phase1_surface_rules
      (descend path AtOptionalBody) body input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel body = true ->
    nullable_expression phase1_surface_nullable_facts body = false ->
    phase1_surface_predictive_oracle path input =
      Some ChooseOptionalPresent.
Proof.
  intros path body input rest tree
    Hresolver Hpath Hderive Hsafe Hnonnullable.
  eapply predictive_bridge_oracle_from_fallback.
  - exact Hresolver.
  - exact Hpath.
  - eapply predictive_fallback_optional_present_from_derivation; eauto.
Qed.

Lemma predictive_bridge_optional_absent_oracle_fallback :
  forall path body input outer_follow,
    phase1_surface_certified_overlap_resolver path input = None ->
    phase1_surface_expression_path_context path (EOptional body) ->
    nullable_expression phase1_surface_nullable_facts body = false ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body)
      outer_follow = [] ->
    continuation_lookahead_mem input outer_follow = true ->
    phase1_surface_predictive_oracle path input =
      Some ChooseOptionalAbsent.
Proof.
  intros path body input outer_follow
    Hresolver Hpath Hnonnullable Hdisjoint Hcontinuation.
  eapply predictive_bridge_oracle_from_fallback.
  - exact Hresolver.
  - exact Hpath.
  - eapply predictive_fallback_optional_absent_from_continuation; eauto.
Qed.

Lemma predictive_bridge_repetition_continue_oracle_fallback :
  forall path body input rest tree,
    phase1_surface_certified_overlap_resolver path input = None ->
    phase1_surface_expression_path_context path (ERepetition body) ->
    Derives phase1_surface_rules
      (descend path AtRepetitionBody) body input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel body = true ->
    nullable_expression phase1_surface_nullable_facts body = false ->
    phase1_surface_predictive_oracle path input =
      Some ChooseRepetitionContinue.
Proof.
  intros path body input rest tree
    Hresolver Hpath Hderive Hsafe Hnonnullable.
  eapply predictive_bridge_oracle_from_fallback.
  - exact Hresolver.
  - exact Hpath.
  - eapply predictive_fallback_repetition_continue_from_derivation; eauto.
Qed.

Lemma predictive_bridge_repetition_stop_oracle_fallback :
  forall path body input outer_follow,
    phase1_surface_certified_overlap_resolver path input = None ->
    phase1_surface_expression_path_context path (ERepetition body) ->
    nullable_expression phase1_surface_nullable_facts body = false ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body)
      outer_follow = [] ->
    continuation_lookahead_mem input outer_follow = true ->
    phase1_surface_predictive_oracle path input =
      Some ChooseRepetitionStop.
Proof.
  intros path body input outer_follow
    Hresolver Hpath Hnonnullable Hdisjoint Hcontinuation.
  eapply predictive_bridge_oracle_from_fallback.
  - exact Hresolver.
  - exact Hpath.
  - eapply predictive_fallback_repetition_stop_from_continuation; eauto.
Qed.
