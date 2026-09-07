From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection
  GrammarDeterminacyPredictiveBridge
  GrammarDeterminacyPredictiveConversion
  GrammarDeterminacyActualCanonicalPath
  GrammarDeterminacyRootedTrailingCommaInvariance
  GrammarDeterminacyChoiceSiteResolverExclusion.

Import ListNotations.

(*
  Structural choice conversion helpers for the final ordinary-derivation ->
  predictive-oracle mutual induction.

  Keep choice safety at one fixed fuel across recursive structure by promoting
  child certificates back one step.  Then package the complete optional and
  non-trailing repetition oracle decisions so the final induction only has to
  assemble OracleDerives constructors.
*)

Lemma predictive_bridge_choice_safe_sequence_cons_same_fuel :
  forall fuel item rest,
    choice_bodies_nonnullable_fuel
      (S fuel) (ESequence (item :: rest)) = true ->
    choice_bodies_nonnullable_fuel (S fuel) item = true /\
    choice_bodies_nonnullable_fuel
      (S fuel) (ESequence rest) = true.
Proof.
  intros fuel item rest Hsafe.
  destruct
    (predictive_bridge_choice_safe_sequence_cons fuel item rest Hsafe)
    as [Hitem Hrest].
  split.
  - apply choice_bodies_nonnullable_fuel_step_monotone.
    exact Hitem.
  - exact Hrest.
Qed.

Lemma predictive_bridge_choice_safe_alternative_member_same_fuel :
  forall fuel items index item,
    choice_bodies_nonnullable_fuel
      (S fuel) (EAlternative items) = true ->
    nth_error items index = Some item ->
    nullable_expression phase1_surface_nullable_facts item = false /\
    choice_bodies_nonnullable_fuel (S fuel) item = true.
Proof.
  intros fuel items index item Hsafe Hnth.
  destruct
    (predictive_bridge_choice_safe_alternative_member
      fuel items index item Hsafe Hnth)
    as [Hnonnullable Hitem].
  split.
  - exact Hnonnullable.
  - apply choice_bodies_nonnullable_fuel_step_monotone.
    exact Hitem.
Qed.

Lemma predictive_bridge_choice_safe_optional_body_same_fuel :
  forall fuel body,
    choice_bodies_nonnullable_fuel
      (S fuel) (EOptional body) = true ->
    nullable_expression phase1_surface_nullable_facts body = false /\
    choice_bodies_nonnullable_fuel (S fuel) body = true.
Proof.
  intros fuel body Hsafe.
  destruct
    (predictive_bridge_choice_safe_optional_body fuel body Hsafe)
    as [Hnonnullable Hbody].
  split.
  - exact Hnonnullable.
  - apply choice_bodies_nonnullable_fuel_step_monotone.
    exact Hbody.
Qed.

Lemma predictive_bridge_choice_safe_repetition_body_same_fuel :
  forall fuel body,
    choice_bodies_nonnullable_fuel
      (S fuel) (ERepetition body) = true ->
    nullable_expression phase1_surface_nullable_facts body = false /\
    choice_bodies_nonnullable_fuel (S fuel) body = true.
Proof.
  intros fuel body Hsafe.
  destruct
    (predictive_bridge_choice_safe_repetition_body fuel body Hsafe)
    as [Hnonnullable Hbody].
  split.
  - exact Hnonnullable.
  - apply choice_bodies_nonnullable_fuel_step_monotone.
    exact Hbody.
Qed.

Theorem phase1_surface_optional_present_oracle :
  forall fuel path body input rest tree,
    phase1_surface_expression_path_context path (EOptional body) ->
    choice_bodies_nonnullable_fuel
      (S fuel) (EOptional body) = true ->
    S fuel <= expression_fuel ->
    Derives phase1_surface_rules
      (descend path AtOptionalBody) body input rest tree ->
    phase1_surface_predictive_oracle path input =
      Some ChooseOptionalPresent.
Proof.
  intros fuel path body input rest tree Hpath Hsafe Hfuel Hderive.
  destruct
    (predictive_bridge_choice_safe_optional_body_same_fuel
      fuel body Hsafe)
    as [Hnonnullable Hbody].
  eapply predictive_bridge_optional_present_oracle_fallback.
  - apply phase1_surface_optional_resolver_none.
    exact Hpath.
  - exact Hpath.
  - exact Hderive.
  - eapply choice_bodies_nonnullable_fuel_monotone.
    + exact Hfuel.
    + exact Hbody.
  - exact Hnonnullable.
Qed.

Theorem phase1_surface_optional_absent_oracle :
  forall choice_fuel assembly_fuel actual canonical body input outer_follow,
    phase1_surface_expression_path_context actual (EOptional body) ->
    choice_bodies_nonnullable_fuel
      (S choice_fuel) (EOptional body) = true ->
    S choice_fuel <= expression_fuel ->
    oracle_assembly_coverage_fuel
      (S assembly_fuel) canonical outer_follow (EOptional body) = true ->
    continuation_lookahead_mem input outer_follow = true ->
    phase1_surface_predictive_oracle actual input =
      Some ChooseOptionalAbsent.
Proof.
  intros choice_fuel assembly_fuel actual canonical body input outer_follow
    Hpath Hsafe Hfuel Hassembly Hcontinuation.
  destruct
    (predictive_bridge_choice_safe_optional_body_same_fuel
      choice_fuel body Hsafe)
    as [Hnonnullable _].
  destruct
    (oracle_assembly_optional_covered
      assembly_fuel canonical outer_follow body Hassembly)
    as [Hdisjointb _].
  pose proof
    (expression_follow_disjointb_sound body outer_follow Hdisjointb)
    as Hdisjoint.
  eapply predictive_bridge_optional_absent_oracle_fallback.
  - apply phase1_surface_optional_resolver_none.
    exact Hpath.
  - exact Hpath.
  - exact Hnonnullable.
  - exact Hdisjoint.
  - exact Hcontinuation.
Qed.

Lemma phase1_surface_nontrailing_repetition_actual_false :
  forall actual caller_prefix canonical,
    phase1_surface_actual_canonical_path actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    trailing_comma_repeat_pathb canonical = false ->
    trailing_comma_repeat_pathb actual = false.
Proof.
  intros actual caller_prefix canonical Hpath Hlocal Hcanonical.
  pose proof
    (phase1_surface_actual_canonical_trailing_comma_equation
      actual caller_prefix canonical Hpath Hlocal)
    as Heq.
  rewrite Hcanonical in Heq.
  exact Heq.
Qed.

Theorem phase1_surface_nontrailing_repetition_continue_oracle :
  forall choice_fuel actual caller_prefix canonical body input rest tree,
    phase1_surface_actual_canonical_path actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    phase1_surface_expression_path_context actual (ERepetition body) ->
    choice_bodies_nonnullable_fuel
      (S choice_fuel) (ERepetition body) = true ->
    S choice_fuel <= expression_fuel ->
    trailing_comma_repeat_pathb canonical = false ->
    Derives phase1_surface_rules
      (descend actual AtRepetitionBody) body input rest tree ->
    phase1_surface_predictive_oracle actual input =
      Some ChooseRepetitionContinue.
Proof.
  intros choice_fuel actual caller_prefix canonical body input rest tree
    Hactual_canonical Hlocal Hpath Hsafe Hfuel Hcanonical Hderive.
  destruct
    (predictive_bridge_choice_safe_repetition_body_same_fuel
      choice_fuel body Hsafe)
    as [Hnonnullable Hbody].
  pose proof
    (phase1_surface_nontrailing_repetition_actual_false
      actual caller_prefix canonical
      Hactual_canonical Hlocal Hcanonical)
    as Hactual.
  eapply predictive_bridge_repetition_continue_oracle_fallback.
  - apply phase1_surface_nontrailing_repetition_resolver_none.
    + exact Hpath.
    + exact Hactual.
  - exact Hpath.
  - exact Hderive.
  - eapply choice_bodies_nonnullable_fuel_monotone.
    + exact Hfuel.
    + exact Hbody.
  - exact Hnonnullable.
Qed.

Theorem phase1_surface_nontrailing_repetition_stop_oracle :
  forall choice_fuel assembly_fuel
         actual caller_prefix canonical body input outer_follow,
    phase1_surface_actual_canonical_path actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    phase1_surface_expression_path_context actual (ERepetition body) ->
    choice_bodies_nonnullable_fuel
      (S choice_fuel) (ERepetition body) = true ->
    S choice_fuel <= expression_fuel ->
    oracle_assembly_coverage_fuel
      (S assembly_fuel) canonical outer_follow (ERepetition body) = true ->
    trailing_comma_repeat_pathb canonical = false ->
    continuation_lookahead_mem input outer_follow = true ->
    phase1_surface_predictive_oracle actual input =
      Some ChooseRepetitionStop.
Proof.
  intros choice_fuel assembly_fuel
    actual caller_prefix canonical body input outer_follow
    Hactual_canonical Hlocal Hpath Hsafe Hfuel Hassembly
    Hcanonical Hcontinuation.
  destruct
    (predictive_bridge_choice_safe_repetition_body_same_fuel
      choice_fuel body Hsafe)
    as [Hnonnullable _].
  pose proof
    (phase1_surface_nontrailing_repetition_actual_false
      actual caller_prefix canonical
      Hactual_canonical Hlocal Hcanonical)
    as Hactual.
  destruct
    (oracle_assembly_repetition_covered
      assembly_fuel canonical outer_follow body Hassembly)
    as [Hguard _].
  pose proof
    (repetition_assembly_guard_fallback
      canonical outer_follow body Hcanonical Hguard)
    as Hdisjointb.
  pose proof
    (expression_follow_disjointb_sound body outer_follow Hdisjointb)
    as Hdisjoint.
  eapply predictive_bridge_repetition_stop_oracle_fallback.
  - apply phase1_surface_nontrailing_repetition_resolver_none.
    + exact Hpath.
    + exact Hactual.
  - exact Hpath.
  - exact Hnonnullable.
  - exact Hdisjoint.
  - exact Hcontinuation.
Qed.
