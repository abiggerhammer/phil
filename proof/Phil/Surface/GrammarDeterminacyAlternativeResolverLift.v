From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers.

Import ListNotations.
Open Scope string_scope.

(*
  Dispatch layer for the six alternative resolver roots used by the final
  PHIL-SURFACE-DETERM-001 ordinary-derivation -> predictive-oracle conversion.

  The semantic soundness files prove results about the small root-specific
  decision functions.  The final conversion consumes the combined certified
  resolver.  Package that path dispatch once, without re-unfolding the resolver
  stack in every semantic branch.
*)

Lemma path_has_suffix_descended_nonterminal_other :
  forall path actual expected,
    actual <> expected ->
    path_has_suffixb
      (descend path (AtNonterminal actual))
      [AtNonterminal expected] = false.
Proof.
  intros path actual expected Hneq.
  unfold path_has_suffixb, descend.
  rewrite List.rev_app_distr.
  simpl.
  destruct (String.eqb expected actual) eqn:Heq.
  - apply String.eqb_eq in Heq.
    symmetry in Heq.
    contradiction.
  - reflexivity.
Qed.

Lemma trailing_comma_repeat_pathb_descended_nonterminal_false :
  forall path name,
    trailing_comma_repeat_pathb
      (descend path (AtNonterminal name)) = false.
Proof.
  intros path name.
  unfold trailing_comma_repeat_pathb,
    case_pattern_comma_repeat_suffix,
    construct_expression_comma_repeat_suffix,
    record_decl_comma_repeat_suffix,
    record_pattern_comma_repeat_suffix,
    variant_payload_comma_repeat_suffix,
    path_has_suffixb, descend.
  repeat rewrite List.rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma phase1_surface_simple_resolver_structural_root_none :
  forall path name input,
    name <> "declaration" ->
    name <> "generic_requirement" ->
    phase1_surface_simple_resolver
      (descend path (AtNonterminal name)) input = None.
Proof.
  intros path name input Hdeclaration Hgeneric.
  unfold phase1_surface_simple_resolver.
  assert (Hprovider :
    path_has_suffixb
      (descend path (AtNonterminal name))
      provider_declaration_suffix = false).
  {
    unfold provider_declaration_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    exact Hdeclaration.
  }
  assert (Hgeneric_suffix :
    path_has_suffixb
      (descend path (AtNonterminal name))
      generic_requirement_suffix = false).
  {
    unfold generic_requirement_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    exact Hgeneric.
  }
  rewrite Hprovider, Hgeneric_suffix.
  rewrite trailing_comma_repeat_pathb_descended_nonterminal_false.
  reflexivity.
Qed.

Lemma phase1_surface_certified_resolver_provider_path :
  forall path input decision,
    provider_declaration_decision input = Some decision ->
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "declaration")) input =
      Some decision.
Proof.
  intros path input decision Hdecision.
  unfold phase1_surface_certified_overlap_resolver.
  rewrite
    (phase1_surface_simple_resolver_provider_path
      path input decision Hdecision).
  reflexivity.
Qed.

Lemma phase1_surface_certified_resolver_generic_requirement_path :
  forall path input decision,
    generic_requirement_decision input = Some decision ->
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "generic_requirement")) input =
      Some decision.
Proof.
  intros path input decision Hdecision.
  unfold phase1_surface_certified_overlap_resolver.
  rewrite
    (phase1_surface_simple_resolver_generic_requirement_path
      path input decision Hdecision).
  reflexivity.
Qed.

Lemma phase1_surface_certified_resolver_pattern_path :
  forall path input decision,
    pattern_decision input = Some decision ->
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "pattern")) input =
      Some decision.
Proof.
  intros path input decision Hdecision.
  unfold phase1_surface_certified_overlap_resolver.
  rewrite
    (phase1_surface_simple_resolver_structural_root_none
      path "pattern" input ltac:(discriminate) ltac:(discriminate)).
  unfold phase1_surface_structural_resolver.
  assert (Hpattern :
    path_has_suffixb
      (descend path (AtNonterminal "pattern"))
      pattern_suffix = true).
  {
    unfold pattern_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hpattern.
  exact Hdecision.
Qed.

Lemma phase1_surface_certified_resolver_primary_expression_path :
  forall path input decision,
    primary_expression_decision input = Some decision ->
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "primary_expression")) input =
      Some decision.
Proof.
  intros path input decision Hdecision.
  unfold phase1_surface_certified_overlap_resolver.
  rewrite
    (phase1_surface_simple_resolver_structural_root_none
      path "primary_expression" input ltac:(discriminate) ltac:(discriminate)).
  unfold phase1_surface_structural_resolver.
  assert (Hpattern :
    path_has_suffixb
      (descend path (AtNonterminal "primary_expression"))
      pattern_suffix = false).
  {
    unfold pattern_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    discriminate.
  }
  assert (Hprimary :
    path_has_suffixb
      (descend path (AtNonterminal "primary_expression"))
      primary_expression_suffix = true).
  {
    unfold primary_expression_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hpattern, Hprimary.
  exact Hdecision.
Qed.

Lemma phase1_surface_certified_resolver_proposition_atom_path :
  forall path input decision,
    proposition_atom_decision input = Some decision ->
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "proposition_atom")) input =
      Some decision.
Proof.
  intros path input decision Hdecision.
  unfold phase1_surface_certified_overlap_resolver.
  rewrite
    (phase1_surface_simple_resolver_structural_root_none
      path "proposition_atom" input ltac:(discriminate) ltac:(discriminate)).
  unfold phase1_surface_structural_resolver.
  assert (Hpattern :
    path_has_suffixb
      (descend path (AtNonterminal "proposition_atom"))
      pattern_suffix = false).
  {
    unfold pattern_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    discriminate.
  }
  assert (Hprimary :
    path_has_suffixb
      (descend path (AtNonterminal "proposition_atom"))
      primary_expression_suffix = false).
  {
    unfold primary_expression_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    discriminate.
  }
  assert (Hproposition :
    path_has_suffixb
      (descend path (AtNonterminal "proposition_atom"))
      proposition_atom_suffix = true).
  {
    unfold proposition_atom_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hpattern, Hprimary, Hproposition.
  exact Hdecision.
Qed.

Lemma phase1_surface_certified_resolver_static_argument_path :
  forall path input decision,
    static_argument_decision input = Some decision ->
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "static_argument")) input =
      Some decision.
Proof.
  intros path input decision Hdecision.
  unfold phase1_surface_certified_overlap_resolver.
  rewrite
    (phase1_surface_simple_resolver_structural_root_none
      path "static_argument" input ltac:(discriminate) ltac:(discriminate)).
  unfold phase1_surface_structural_resolver.
  assert (Hpattern :
    path_has_suffixb
      (descend path (AtNonterminal "static_argument"))
      pattern_suffix = false).
  {
    unfold pattern_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    discriminate.
  }
  assert (Hprimary :
    path_has_suffixb
      (descend path (AtNonterminal "static_argument"))
      primary_expression_suffix = false).
  {
    unfold primary_expression_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    discriminate.
  }
  assert (Hproposition :
    path_has_suffixb
      (descend path (AtNonterminal "static_argument"))
      proposition_atom_suffix = false).
  {
    unfold proposition_atom_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    discriminate.
  }
  assert (Hstatic :
    path_has_suffixb
      (descend path (AtNonterminal "static_argument"))
      static_argument_suffix = true).
  {
    unfold static_argument_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hpattern, Hprimary, Hproposition, Hstatic.
  exact Hdecision.
Qed.
