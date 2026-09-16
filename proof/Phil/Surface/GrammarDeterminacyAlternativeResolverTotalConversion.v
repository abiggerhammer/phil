From Stdlib Require Import Lists.List.

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
  GrammarDeterminacyAlternativeResolverNoneConversion
  GrammarDeterminacyAlternativeResolverSomeConversion.

(*
  Total resolver-root alternative conversion for PHIL-SURFACE-DETERM-001.

  #764 proves the certified-resolver-None half and #766 proves the Some half.
  The final mutual ordinary-derivation -> predictive-oracle induction should not
  need to inspect resolver internals at the six exceptional alternative roots;
  it can consume this theorem as a single total dispatch.
*)

Theorem phase1_surface_resolver_context_oracle_alternative :
  forall path outer_follow items index item input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    alternative_resolver_contextb path outer_follow = true ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle path input =
      Some (ChooseAlternative index).
Proof.
  intros path outer_follow items index item input rest tree
    Hpath Hresolver_context Hnth Hderive Hsafe Hnonnullable Hcontinuation.
  destruct
    (phase1_surface_certified_overlap_resolver path input)
    as [decision |] eqn:Hresolver.
  - eapply phase1_surface_resolver_some_oracle_alternative.
    + exact Hpath.
    + exact Hresolver_context.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + exact Hcontinuation.
  - eapply phase1_surface_resolver_none_oracle_alternative.
    + exact Hpath.
    + exact Hresolver_context.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + exact Hcontinuation.
Qed.
