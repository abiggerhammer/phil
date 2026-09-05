From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyRelationCommitmentSoundness
  GrammarDeterminacyStaticArgumentParenthesisSoundness
  GrammarDeterminacyStaticArgumentBraceBridge
  GrammarDeterminacyEffectSetBraceSoundness
  GrammarDeterminacyAlternativeResolverLift.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic commitments for the two complex resolver-backed alternative roots.

  This file intentionally covers only certified overlap inputs.  Branches that
  do not trigger the certified resolver remain the responsibility of the
  predictive fallback half of the final ordinary-derivation -> oracle bridge.
*)

Theorem phase1_surface_relation_identifier_certified_commitment :
  forall root_prefix branch_path input rest tree lexeme tail,
    Derives phase1_surface_rules branch_path
      (ENonterminal "relation_proposition") input rest tree ->
    input = TLexical "IDENTIFIER" lexeme :: tail ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input =
      Some (ChooseAlternative 0).
Proof.
  intros root_prefix branch_path input rest tree lexeme tail Hderive Hinput.
  apply phase1_surface_certified_resolver_proposition_atom_path.
  eapply phase1_surface_relation_proposition_identifier_overlap_commits_relation.
  - exact Hderive.
  - exact Hinput.
Qed.

Theorem phase1_surface_relation_parenthesis_certified_commitment :
  forall root_prefix branch_path input rest tree tail,
    Derives phase1_surface_rules branch_path
      (ENonterminal "relation_proposition") input rest tree ->
    input = TLiteral "(" :: tail ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input =
      Some (ChooseAlternative 0).
Proof.
  intros root_prefix branch_path input rest tree tail Hderive Hinput.
  apply phase1_surface_certified_resolver_proposition_atom_path.
  eapply phase1_surface_relation_proposition_parenthesis_overlap_commits_relation.
  - exact Hderive.
  - exact Hinput.
Qed.

Theorem phase1_surface_relation_true_certified_commitment :
  forall root_prefix branch_path input rest tree tail,
    Derives phase1_surface_rules branch_path
      (ENonterminal "relation_proposition") input rest tree ->
    input = TLiteral "true" :: tail ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input =
      Some (ChooseAlternative 0).
Proof.
  intros root_prefix branch_path input rest tree tail Hderive Hinput.
  apply phase1_surface_certified_resolver_proposition_atom_path.
  eapply phase1_surface_relation_proposition_true_overlap_commits_relation.
  - exact Hderive.
  - exact Hinput.
Qed.

Theorem phase1_surface_relation_false_certified_commitment :
  forall root_prefix branch_path input rest tree tail,
    Derives phase1_surface_rules branch_path
      (ENonterminal "relation_proposition") input rest tree ->
    input = TLiteral "false" :: tail ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input =
      Some (ChooseAlternative 0).
Proof.
  intros root_prefix branch_path input rest tree tail Hderive Hinput.
  apply phase1_surface_certified_resolver_proposition_atom_path.
  eapply phase1_surface_relation_proposition_false_overlap_commits_relation.
  - exact Hderive.
  - exact Hinput.
Qed.

Theorem phase1_surface_grouped_proposition_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      phase1_surface_grouped_proposition_expression input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input =
      Some (ChooseAlternative 1).
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation.
  apply phase1_surface_certified_resolver_proposition_atom_path.
  eapply phase1_surface_grouped_proposition_atom_derivation_commits_grouping_branch.
  - exact Hderive.
  - exact Hcontinuation.
Qed.

Theorem phase1_surface_true_proposition_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ELiteral "true") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input =
      Some (ChooseAlternative 2).
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation.
  apply phase1_surface_certified_resolver_proposition_atom_path.
  eapply phase1_surface_true_proposition_atom_derivation_commits_literal_branch.
  - exact Hderive.
  - exact Hcontinuation.
Qed.

Theorem phase1_surface_false_proposition_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ELiteral "false") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input =
      Some (ChooseAlternative 3).
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation.
  apply phase1_surface_certified_resolver_proposition_atom_path.
  eapply phase1_surface_false_proposition_atom_derivation_commits_literal_branch.
  - exact Hderive.
  - exact Hcontinuation.
Qed.

Theorem phase1_surface_claim_application_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "claim_application") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "proposition_atom")) input =
      Some (ChooseAlternative 4).
Proof.
  intros root_prefix branch_path input rest tree Hderive Hcontinuation.
  apply phase1_surface_certified_resolver_proposition_atom_path.
  eapply phase1_surface_claim_application_derivation_commits_claim_branch.
  - exact Hderive.
  - exact Hcontinuation.
Qed.

Theorem phase1_surface_static_type_parenthesis_certified_commitment :
  forall root_prefix branch_path input rest tree tail,
    Derives phase1_surface_rules branch_path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    input = TLiteral "(" :: tail ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "static_argument")) input =
      Some (ChooseAlternative 0).
Proof.
  intros root_prefix branch_path input rest tree tail Hderive Hinput.
  apply phase1_surface_certified_resolver_static_argument_path.
  eapply
    phase1_surface_nonreference_type_expression_open_derivation_commits_static_argument_tuple_branch.
  - exact Hderive.
  - exact Hinput.
Qed.

Theorem phase1_surface_static_value_parenthesis_certified_commitment :
  forall root_prefix branch_path input rest tree tail,
    Derives phase1_surface_rules branch_path
      (ENonterminal "static_value_expression") input rest tree ->
    input = TLiteral "(" :: tail ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "static_argument")) input =
      Some (ChooseAlternative 2).
Proof.
  intros root_prefix branch_path input rest tree tail Hderive Hinput.
  apply phase1_surface_certified_resolver_static_argument_path.
  eapply
    phase1_surface_static_value_expression_open_derivation_commits_static_argument_value_branch.
  - exact Hderive.
  - exact Hinput.
Qed.

Theorem phase1_surface_static_type_brace_certified_commitment :
  forall root_prefix branch_path input rest tree tail,
    Derives phase1_surface_rules branch_path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    input = TLiteral "{" :: tail ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "static_argument")) input =
      Some (ChooseAlternative 0).
Proof.
  intros root_prefix branch_path input rest tree tail Hderive Hinput.
  apply phase1_surface_certified_resolver_static_argument_path.
  eapply
    phase1_surface_nonreference_type_expression_brace_derivation_commits_static_argument_branch.
  - exact Hderive.
  - exact Hinput.
Qed.

Theorem phase1_surface_effect_set_certified_commitment :
  forall root_prefix branch_path input rest tree,
    Derives phase1_surface_rules branch_path
      (ENonterminal "effect_set_literal") input rest tree ->
    phase1_surface_certified_overlap_resolver
      (descend root_prefix (AtNonterminal "static_argument")) input =
      Some (ChooseAlternative 3).
Proof.
  intros root_prefix branch_path input rest tree Hderive.
  apply phase1_surface_certified_resolver_static_argument_path.
  eapply phase1_surface_effect_set_literal_derivation_commits_static_argument_branch.
  exact Hderive.
Qed.
