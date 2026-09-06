From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyFollowCoverage
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyPathPrefixInvariance.

Import ListNotations.

(*
  Nonterminal reset package for the final PHIL-SURFACE-DETERM-001 mutual
  ordinary-derivation -> predictive-oracle induction.

  The mechanical FOLLOW and oracle-assembly checkers deliberately stop at
  nonterminals.  Successful rule lookup is therefore the reset boundary: the
  child rule body gets its globally certified choice-safety, FOLLOW coverage,
  and canonical rule-local assembly coverage, while the caller's accepting
  continuation is lifted into the callee's global FOLLOW set.

  #772 proved that resolver-root classification is unaffected by the caller
  prefix.  Include that exact root equality here so the recursive induction can
  keep assembly coverage on [AtNonterminal name] while making oracle decisions
  at the full derivation path.
*)

Theorem phase1_surface_nonterminal_reset_invariants :
  forall fuel path outer_follow name body continuation,
    phase1_surface_expression_path_context path (ENonterminal name) ->
    lookupRule name phase1_surface_rules = Some body ->
    follow_coverage_fuel
      (S fuel) outer_follow (ENonterminal name) = true ->
    continuation_lookahead_mem continuation outer_follow = true ->
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
  repeat split.
  - eapply phase1_surface_nonterminal_child_path_context; eauto.
  - eapply phase1_surface_rule_body_choice_safe; eauto.
  - eapply phase1_surface_rule_body_follow_covered; eauto.
  - eapply phase1_surface_rule_body_oracle_assembly_covered; eauto.
  - eapply follow_coverage_lifts_nonterminal_continuation; eauto.
  - change
      alternative_resolver_contextb
        (path ++ [AtNonterminal name])
        (lookup_tokens name phase1_surface_follow_facts) =
      alternative_resolver_contextb
        [AtNonterminal name]
        (lookup_tokens name phase1_surface_follow_facts).
    apply alternative_resolver_contextb_prefix_irrelevant.
    discriminate.
Qed.
