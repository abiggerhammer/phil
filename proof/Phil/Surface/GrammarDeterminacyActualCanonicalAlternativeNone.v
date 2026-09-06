From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyPredictiveConversion
  GrammarDeterminacyAlternativeResolverTotalConversion
  GrammarDeterminacyActualCanonicalPath.

(*
  Resolver-None conversion across the actual/canonical path boundary for the
  final PHIL-SURFACE-DETERM-001 ordinary-derivation -> predictive-oracle
  induction.

  Assembly coverage is checked on the canonical rule-local path, while the
  predictive oracle and ordinary derivation live at the full actual path.
  #776 packages the relation between those paths and transports resolver-root
  classification.  The pairwise-FIRST-disjoint branch is path-independent.
*)

Theorem phase1_surface_actual_canonical_resolver_none_oracle_alternative :
  forall fuel actual caller_prefix canonical outer_follow
         items index item input rest tree,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    canonical <> [] ->
    phase1_surface_expression_path_context
      actual (EAlternative items) ->
    oracle_assembly_coverage_fuel
      (S fuel) canonical outer_follow (EAlternative items) = true ->
    phase1_surface_certified_overlap_resolver actual input = None ->
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
    Hactual Hcanonical Hpath Hassembly Hresolver Hnth Hderive
    Hsafe Hnonnullable Hcontinuation.
  pose proof
    (oracle_assembly_alternative_guard
      fuel canonical outer_follow items Hassembly) as Hguard.
  apply orb_true_iff in Hguard.
  destruct Hguard as [Hresolver_context | Hpairwise].
  - assert
      (Hresolver_context_actual :
        alternative_resolver_contextb actual outer_follow = true).
    {
      pose proof
        (phase1_surface_actual_canonical_path_resolver_context
          actual caller_prefix canonical outer_follow
          Hactual Hcanonical) as Hcontext.
      rewrite Hcontext.
      exact Hresolver_context.
    }
    eapply phase1_surface_resolver_context_oracle_alternative.
    + exact Hpath.
    + exact Hresolver_context_actual.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + exact Hcontinuation.
  - eapply predictive_bridge_pairwise_oracle_alternative.
    + exact Hresolver.
    + exact Hpath.
    + exact Hpairwise.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
Qed.
