From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyPatternResolverSoundness
  GrammarDeterminacyPrimaryParenthesisSoundness
  GrammarDeterminacyAlternativeResolverLift.

Import ListNotations.

(*
  Semantic core for the resolver-backed alternative half of the final
  PHIL-SURFACE-DETERM-001 ordinary-derivation -> predictive-oracle bridge.

  The specialized soundness files prove commitments for the small root-local
  decision functions.  #748 proved that each such decision lifts through the
  combined certified overlap resolver at the corresponding grammar root.
  Compose those layers once for the four simpler resolver roots here.
*)

Theorem phase1_surface_provider_contract_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "provider_contract_decl") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "declaration")) input =
      Some (ChooseAlternative 6).
Proof.
  intros root_prefix branch_path input rest tree Hderive.
  apply phase1_surface_certified_resolver_provider_path.
  eapply provider_contract_derivation_commits_branch_six.
  exact Hderive.
Qed.

Theorem phase1_surface_provider_implementation_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "provider_implementation_decl") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "declaration")) input =
      Some (ChooseAlternative 7).
Proof.
  intros root_prefix branch_path input rest tree Hderive.
  apply phase1_surface_certified_resolver_provider_path.
  eapply provider_implementation_derivation_commits_branch_seven.
  exact Hderive.
Qed.

Theorem phase1_surface_generic_boundary_name_certified_commitment :
  forall root_prefix branch_path tail_items input rest tree,
    Derives phase1_surface_rules branch_path
      (ESequence
        (ELiteral "boundary" ::
         ENonterminal "identifier" ::
         tail_items))
      input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "generic_requirement")) input =
      Some (ChooseAlternative 4).
Proof.
  intros root_prefix branch_path tail_items input rest tree Hderive.
  apply phase1_surface_certified_resolver_generic_requirement_path.
  eapply generic_boundary_name_derivation_commits_branch_four.
  exact Hderive.
Qed.

Theorem phase1_surface_generic_boundary_representation_certified_commitment :
  forall root_prefix branch_path tail_items input rest tree,
    Derives phase1_surface_rules branch_path
      (ESequence
        (ELiteral "boundary" ::
         ELiteral "representation" ::
         tail_items))
      input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "generic_requirement")) input =
      Some (ChooseAlternative 8).
Proof.
  intros root_prefix branch_path tail_items input rest tree Hderive.
  apply phase1_surface_certified_resolver_generic_requirement_path.
  eapply generic_boundary_representation_derivation_commits_branch_eight.
  exact Hderive.
Qed.

Theorem phase1_surface_identifier_pattern_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "identifier") input rest tree ->
    continuation_lookahead_mem rest phase1_surface_pattern_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "pattern")) input =
      Some (ChooseAlternative 0).
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation.
  apply phase1_surface_certified_resolver_pattern_path.
  eapply phase1_surface_identifier_pattern_derivation_commits_pattern_branch.
  - exact Hderive.
  - exact Hcontinuation.
Qed.

Theorem phase1_surface_record_pattern_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "record_pattern") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "pattern")) input =
      Some (ChooseAlternative 2).
Proof.
  intros root_prefix branch_path input rest tree Hderive.
  apply phase1_surface_certified_resolver_pattern_path.
  destruct phase1_surface_pattern_structural_overlap_semantic_sound
    as [_ Hrecord].
  eapply Hrecord.
  exact Hderive.
Qed.

Theorem phase1_surface_tuple_expression_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "tuple_expression") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "primary_expression")) input =
      Some (ChooseAlternative 0).
Proof.
  intros root_prefix branch_path input rest tree Hderive.
  apply phase1_surface_certified_resolver_primary_expression_path.
  eapply phase1_surface_tuple_expression_derivation_commits_primary_tuple_branch.
  exact Hderive.
Qed.

Theorem phase1_surface_parenthesized_expression_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "parenthesized_expression") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "primary_expression")) input =
      Some (ChooseAlternative 1).
Proof.
  intros root_prefix branch_path input rest tree Hderive.
  apply phase1_surface_certified_resolver_primary_expression_path.
  eapply
    phase1_surface_parenthesized_expression_derivation_commits_primary_grouping_branch.
  exact Hderive.
Qed.
