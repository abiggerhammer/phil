From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacyFollowCoverage
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyNonterminalReset
  GrammarDeterminacyActualCanonicalPath
  GrammarDeterminacyResolverFollowCompatibility
  GrammarDeterminacyRootedTrailingCommaInvariance.

Import ListNotations.

(*
  Consolidated nonterminal reset package for the final
  ordinary-derivation -> predictive-oracle mutual induction.

  Earlier slices established these invariants independently.  At every
  successful rule lookup, the induction resets the canonical rule-local path
  and generated FOLLOW together, so expose the exact combined state here.
*)

Theorem phase1_surface_complete_nonterminal_reset_invariants :
  forall fuel path outer_follow name body continuation,
    phase1_surface_expression_path_context path (ENonterminal name) ->
    lookupRule name phase1_surface_rules = Some body ->
    follow_coverage_fuel
      (S fuel) outer_follow (ENonterminal name) = true ->
    continuation_lookahead_mem continuation outer_follow = true ->
    phase1_surface_actual_canonical_path
      (descend path (AtNonterminal name))
      path
      [AtNonterminal name] /\
    phase1_surface_rule_local_path [AtNonterminal name] /\
    phase1_surface_resolver_follow_compatible
      [AtNonterminal name]
      (lookup_tokens name phase1_surface_follow_facts) /\
    phase1_surface_expression_path_context
      (descend path (AtNonterminal name)) body /\
    choice_bodies_nonnullable_fuel expression_fuel body = true /\
    follow_coverage_fuel
      expression_fuel
      (lookup_tokens name phase1_surface_follow_facts)
      body = true /\
    oracle_assembly_coverage_fuel
      oracle_assembly_fuel
      [AtNonterminal name]
      (lookup_tokens name phase1_surface_follow_facts)
      body = true /\
    continuation_lookahead_mem
      continuation
      (lookup_tokens name phase1_surface_follow_facts) = true /\
    alternative_resolver_contextb
      (descend path (AtNonterminal name))
      (lookup_tokens name phase1_surface_follow_facts) =
    alternative_resolver_contextb
      [AtNonterminal name]
      (lookup_tokens name phase1_surface_follow_facts).
Proof.
  intros fuel path outer_follow name body continuation
    Hpath Hlookup Hfollow Hcontinuation.
  pose proof
    (phase1_surface_nonterminal_reset_invariants
      fuel path outer_follow name body continuation
      Hpath Hlookup Hfollow Hcontinuation)
    as Hreset.
  destruct Hreset as
    [Hchild_path
      [Hsafe
        [Hchild_follow
          [Hassembly
            [Hchild_continuation Hresolver_context]]]]].
  destruct
    (phase1_surface_actual_canonical_nonterminal_reset
      path name
      (lookup_tokens name phase1_surface_follow_facts))
    as [Hactual_canonical _].
  repeat split.
  - exact Hactual_canonical.
  - apply phase1_surface_rule_local_path_reset.
  - apply phase1_surface_nonterminal_reset_resolver_follow_compatible.
  - exact Hchild_path.
  - exact Hsafe.
  - exact Hchild_follow.
  - exact Hassembly.
  - exact Hchild_continuation.
  - exact Hresolver_context.
Qed.
