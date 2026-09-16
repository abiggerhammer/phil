From Stdlib Require Import Lists.List Strings.String.

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
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyPathPrefixInvariance
  GrammarDeterminacyActualCanonicalPath
  GrammarDeterminacyAlternativeResolverSomeConversion
  GrammarDeterminacyAlternativeResolverSomeSuffix
  GrammarDeterminacyActualCanonicalResolverSuffix
  GrammarDeterminacyAlternativeResolverContextFollow.

Import ListNotations.
Open Scope string_scope.

(*
  Certified-resolver-Some alternative conversion across the actual/canonical
  path split carried by the final PHIL-SURFACE-DETERM-001 mutual induction.

  #783 classifies every resolver Some result at a valid alternative path into
  one of the six resolver suffix families.  #785 transports that classification
  to the canonical rule-local path.  #788 recovers resolver-context coverage
  from the canonical suffix plus the two FOLLOW-sensitive root invariants.
  Finally #776 transports that resolver-context fact back to the full actual
  path, where the existing resolver-Some semantic conversion applies.
*)

Theorem phase1_surface_actual_canonical_resolver_some_oracle_alternative :
  forall actual caller_prefix canonical outer_follow
         items index item input rest tree decision,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    canonical <> [] ->
    phase1_surface_expression_path_context
      actual (EAlternative items) ->
    phase1_surface_certified_overlap_resolver actual input = Some decision ->
    (path_has_suffixb canonical pattern_suffix = true ->
      outer_follow =
        lookup_tokens "pattern" phase1_surface_follow_facts) ->
    (path_has_suffixb canonical proposition_atom_suffix = true ->
      outer_follow =
        lookup_tokens "proposition_atom" phase1_surface_follow_facts) ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend actual (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle actual input =
      Some (ChooseAlternative index).
Proof.
  intros actual caller_prefix canonical outer_follow
    items index item input rest tree decision
    Hpath Hnonempty Hexpression Hresolver
    Hpattern_follow Hproposition_follow
    Hnth Hderive Hsafe Hnonnullable Hcontinuation.
  pose proof
    (phase1_surface_alternative_resolver_some_suffix_classified
      actual items input decision Hexpression Hresolver)
    as Hactual_suffix.
  pose proof
    (phase1_surface_actual_canonical_resolver_suffix
      actual caller_prefix canonical
      Hpath Hnonempty Hactual_suffix)
    as Hcanonical_suffix.
  pose proof
    (phase1_surface_resolver_suffix_context_follow
      canonical outer_follow
      Hcanonical_suffix Hpattern_follow Hproposition_follow)
    as Hcanonical_context.
  assert (Hactual_context :
    alternative_resolver_contextb actual outer_follow = true).
  {
    rewrite
      (phase1_surface_actual_canonical_path_resolver_context
        actual caller_prefix canonical outer_follow
        Hpath Hnonempty).
    exact Hcanonical_context.
  }
  eapply phase1_surface_resolver_some_oracle_alternative.
  - exact Hexpression.
  - exact Hactual_context.
  - exact Hresolver.
  - exact Hnth.
  - exact Hderive.
  - exact Hsafe.
  - exact Hnonnullable.
  - exact Hcontinuation.
Qed.
