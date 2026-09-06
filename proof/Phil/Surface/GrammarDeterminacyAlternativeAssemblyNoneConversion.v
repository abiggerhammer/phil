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
  GrammarDeterminacyAlternativeResolverTotalConversion.

(*
  Resolver-None assembly conversion for the alternative case of the final
  PHIL-SURFACE-DETERM-001 ordinary-derivation -> predictive-oracle induction.

  Oracle assembly coverage says that every generated alternative is either one
  of the six certified resolver roots or is pairwise FIRST-disjoint.  #769
  packages the resolver-root case behind one total theorem.  When the certified
  resolver is None, the pairwise-disjoint case is already handled by the
  predictive fallback conversion.  Package that assembly split once here so
  the final mutual induction does not reopen it.
*)

Theorem phase1_surface_resolver_none_assembly_oracle_alternative :
  forall fuel path outer_follow items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    oracle_assembly_coverage_fuel
      (S fuel) path outer_follow (EAlternative items) = true ->
    phase1_surface_certified_overlap_resolver path input = None ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle path input =
      Some (ChooseAlternative index).
Proof.
  intros fuel path outer_follow items index item input rest tree
    Hpath Hassembly Hresolver Hnth Hderive Hsafe Hnonnullable Hcontinuation.
  pose proof
    (oracle_assembly_alternative_guard
      fuel path outer_follow items Hassembly) as Hguard.
  apply orb_true_iff in Hguard.
  destruct Hguard as [Hresolver_context | Hpairwise].
  - eapply phase1_surface_resolver_context_oracle_alternative.
    + exact Hpath.
    + exact Hresolver_context.
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
