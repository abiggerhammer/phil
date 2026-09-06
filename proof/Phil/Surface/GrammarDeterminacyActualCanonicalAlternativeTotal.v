From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyActualCanonicalPath
  GrammarDeterminacyActualCanonicalAlternativeNone
  GrammarDeterminacyActualCanonicalAlternativeSome.

Import ListNotations.
Open Scope string_scope.

(*
  Total alternative conversion across the actual/canonical path split carried
  by the final PHIL-SURFACE-DETERM-001 mutual induction.

  #777 packages the certified-resolver-None half using canonical assembly
  coverage.  #791 packages the certified-resolver-Some half using the two
  FOLLOW-sensitive resolver-root invariants.  This theorem destructs the
  certified resolver exactly once and exposes a single interface to the final
  induction.
*)

Theorem phase1_surface_actual_canonical_oracle_alternative :
  forall fuel actual caller_prefix canonical outer_follow
         items index item input rest tree,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    canonical <> [] ->
    phase1_surface_expression_path_context
      actual (EAlternative items) ->
    oracle_assembly_coverage_fuel
      (S fuel) canonical outer_follow (EAlternative items) = true ->
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
  intros fuel actual caller_prefix canonical outer_follow
    items index item input rest tree
    Hpath Hnonempty Hexpression Hassembly
    Hpattern_follow Hproposition_follow
    Hnth Hderive Hsafe Hnonnullable Hcontinuation.
  destruct
    (phase1_surface_certified_overlap_resolver actual input)
    as [decision |] eqn:Hresolver.
  - eapply phase1_surface_actual_canonical_resolver_some_oracle_alternative.
    + exact Hpath.
    + exact Hnonempty.
    + exact Hexpression.
    + exact Hresolver.
    + exact Hpattern_follow.
    + exact Hproposition_follow.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + exact Hcontinuation.
  - eapply phase1_surface_actual_canonical_resolver_none_oracle_alternative.
    + exact Hpath.
    + exact Hnonempty.
    + exact Hexpression.
    + exact Hassembly.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + exact Hcontinuation.
Qed.
