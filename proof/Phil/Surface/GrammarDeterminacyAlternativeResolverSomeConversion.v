From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyPredictiveFallbackSoundness
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection
  GrammarDeterminacyAlternativeResolverLift
  GrammarDeterminacyAlternativeResolverContext
  GrammarDeterminacyAlternativeEarlierDisjoint
  GrammarDeterminacyPatternResolverSoundness
  GrammarDeterminacyRelationCommitmentSoundness
  GrammarDeterminacyAlternativeResolverSemanticCore
  GrammarDeterminacyAlternativeResolverSemanticComplex
  GrammarDeterminacyAlternativeResolverNoneConversion
  GrammarDeterminacyStaticValueResolverNoneFallback
  GrammarDeterminacyPredictiveConversion.

Import ListNotations.
Open Scope string_scope.

(*
  Certified-resolver-Some half of the alternative conversion used by
  PHIL-SURFACE-DETERM-001.

  #764 packages the resolver-None half.  At a resolver root, a Some result can
  only be triggered by a tiny root-local token set.  We mechanically certify
  that every branch which is not semantically resolver-backed is FIRST-disjoint
  from that trigger set.  An ordinary derivation through such a branch therefore
  contradicts a resolver Some result.  The remaining finite branches are exactly
  those already covered by the semantic commitments in #750/#754.
*)

Lemma phase1_surface_structural_resolver_nonroot_none :
  forall path name input,
    name <> "pattern" ->
    name <> "primary_expression" ->
    name <> "proposition_atom" ->
    name <> "static_argument" ->
    phase1_surface_structural_resolver
      (descend path (AtNonterminal name)) input = None.
Proof.
  intros path name input Hpattern Hprimary Hproposition Hstatic.
  unfold phase1_surface_structural_resolver.
  assert (Hpattern_suffix :
    path_has_suffixb
      (descend path (AtNonterminal name)) pattern_suffix = false).
  {
    unfold pattern_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    exact Hpattern.
  }
  assert (Hprimary_suffix :
    path_has_suffixb
      (descend path (AtNonterminal name)) primary_expression_suffix = false).
  {
    unfold primary_expression_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    exact Hprimary.
  }
  assert (Hproposition_suffix :
    path_has_suffixb
      (descend path (AtNonterminal name)) proposition_atom_suffix = false).
  {
    unfold proposition_atom_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    exact Hproposition.
  }
  assert (Hstatic_suffix :
    path_has_suffixb
      (descend path (AtNonterminal name)) static_argument_suffix = false).
  {
    unfold static_argument_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    exact Hstatic.
  }
  rewrite Hpattern_suffix, Hprimary_suffix, Hproposition_suffix, Hstatic_suffix.
  reflexivity.
Qed.

Lemma phase1_surface_certified_resolver_declaration_equation :
  forall path input,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "declaration")) input =
    provider_declaration_decision input.
Proof.
  intros path input.
  unfold phase1_surface_certified_overlap_resolver.
  unfold phase1_surface_simple_resolver.
  assert (Hprovider :
    path_has_suffixb
      (descend path (AtNonterminal "declaration"))
      provider_declaration_suffix = true).
  {
    unfold provider_declaration_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hprovider.
  destruct (provider_declaration_decision input) eqn:Hdecision.
  - reflexivity.
  - simpl.
    apply phase1_surface_structural_resolver_nonroot_none;
      discriminate.
Qed.

Lemma phase1_surface_certified_resolver_generic_requirement_equation :
  forall path input,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "generic_requirement")) input =
    generic_requirement_decision input.
Proof.
  intros path input.
  unfold phase1_surface_certified_overlap_resolver.
  unfold phase1_surface_simple_resolver.
  assert (Hprovider :
    path_has_suffixb
      (descend path (AtNonterminal "generic_requirement"))
      provider_declaration_suffix = false).
  {
    unfold provider_declaration_suffix.
    apply path_has_suffix_descended_nonterminal_other.
    discriminate.
  }
  assert (Hgeneric :
    path_has_suffixb
      (descend path (AtNonterminal "generic_requirement"))
      generic_requirement_suffix = true).
  {
    unfold generic_requirement_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hprovider, Hgeneric.
  destruct (generic_requirement_decision input) eqn:Hdecision.
  - reflexivity.
  - simpl.
    apply phase1_surface_structural_resolver_nonroot_none;
      discriminate.
Qed.

Lemma phase1_surface_certified_resolver_pattern_equation :
  forall path input,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "pattern")) input =
    pattern_decision input.
Proof.
  intros path input.
  unfold phase1_surface_certified_overlap_resolver.
  rewrite
    (phase1_surface_simple_resolver_structural_root_none
      path "pattern" input ltac:(discriminate) ltac:(discriminate)).
  unfold phase1_surface_structural_resolver.
  assert (Hpattern :
    path_has_suffixb
      (descend path (AtNonterminal "pattern")) pattern_suffix = true).
  {
    unfold pattern_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hpattern.
  reflexivity.
Qed.

Lemma phase1_surface_certified_resolver_primary_expression_equation :
  forall path input,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "primary_expression")) input =
    primary_expression_decision input.
Proof.
  intros path input.
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
  reflexivity.
Qed.

Lemma phase1_surface_certified_resolver_proposition_atom_equation :
  forall path input,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "proposition_atom")) input =
    proposition_atom_decision input.
Proof.
  intros path input.
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
  reflexivity.
Qed.

Lemma phase1_surface_certified_resolver_static_argument_equation :
  forall path input,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "static_argument")) input =
    static_argument_decision input.
Proof.
  intros path input.
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
  reflexivity.
Qed.

Definition declaration_resolver_trigger : list OverlapToken :=
  [OverlapLiteral "provider"].
Definition generic_requirement_resolver_trigger : list OverlapToken :=
  [OverlapLiteral "boundary"].
Definition pattern_resolver_trigger : list OverlapToken :=
  [OverlapLexicalClass "IDENTIFIER"].
Definition primary_expression_resolver_trigger : list OverlapToken :=
  [OverlapLiteral "("].
Definition proposition_atom_resolver_trigger : list OverlapToken :=
  [ OverlapLexicalClass "IDENTIFIER"
  ; OverlapLiteral "("
  ; OverlapLiteral "true"
  ; OverlapLiteral "false"
  ].
Definition static_argument_resolver_trigger : list OverlapToken :=
  [OverlapLiteral "("; OverlapLiteral "{"].

Lemma phase1_surface_declaration_resolver_some_trigger :
  forall path input decision,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "declaration")) input = Some decision ->
    continuation_lookahead_mem input declaration_resolver_trigger = true.
Proof.
  intros path input decision Hresolver.
  rewrite phase1_surface_certified_resolver_declaration_equation in Hresolver.
  destruct input as [| first tail]; try discriminate Hresolver.
  destruct first as [literal | class_name lexeme].
  - unfold provider_declaration_decision in Hresolver.
    simpl in Hresolver.
    destruct (String.eqb literal "provider") eqn:Hliteral;
      try discriminate Hresolver.
    apply String.eqb_eq in Hliteral.
    subst literal.
    reflexivity.
  - discriminate Hresolver.
Qed.

Lemma phase1_surface_generic_requirement_resolver_some_trigger :
  forall path input decision,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "generic_requirement")) input = Some decision ->
    continuation_lookahead_mem input generic_requirement_resolver_trigger = true.
Proof.
  intros path input decision Hresolver.
  rewrite phase1_surface_certified_resolver_generic_requirement_equation in Hresolver.
  destruct input as [| first tail]; try discriminate Hresolver.
  destruct first as [literal | class_name lexeme].
  - unfold generic_requirement_decision in Hresolver.
    simpl in Hresolver.
    destruct (String.eqb literal "boundary") eqn:Hliteral;
      try discriminate Hresolver.
    apply String.eqb_eq in Hliteral.
    subst literal.
    reflexivity.
  - discriminate Hresolver.
Qed.

Lemma phase1_surface_pattern_resolver_some_trigger :
  forall path input decision,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "pattern")) input = Some decision ->
    continuation_lookahead_mem input pattern_resolver_trigger = true.
Proof.
  intros path input decision Hresolver.
  rewrite phase1_surface_certified_resolver_pattern_equation in Hresolver.
  destruct input as [| first tail]; try discriminate Hresolver.
  destruct first as [literal | class_name lexeme].
  - discriminate Hresolver.
  - unfold pattern_decision in Hresolver.
    simpl in Hresolver.
    destruct (String.eqb class_name "IDENTIFIER") eqn:Hclass;
      try discriminate Hresolver.
    apply String.eqb_eq in Hclass.
    subst class_name.
    reflexivity.
Qed.

Lemma phase1_surface_primary_expression_resolver_some_trigger :
  forall path input decision,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "primary_expression")) input = Some decision ->
    continuation_lookahead_mem input primary_expression_resolver_trigger = true.
Proof.
  intros path input decision Hresolver.
  rewrite phase1_surface_certified_resolver_primary_expression_equation in Hresolver.
  destruct input as [| first tail]; try discriminate Hresolver.
  destruct first as [literal | class_name lexeme].
  - unfold primary_expression_decision in Hresolver.
    simpl in Hresolver.
    destruct (String.eqb literal "(") eqn:Hliteral;
      try discriminate Hresolver.
    apply String.eqb_eq in Hliteral.
    subst literal.
    reflexivity.
  - discriminate Hresolver.
Qed.

Lemma phase1_surface_proposition_atom_resolver_some_trigger :
  forall path input decision,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "proposition_atom")) input = Some decision ->
    continuation_lookahead_mem input proposition_atom_resolver_trigger = true.
Proof.
  intros path input decision Hresolver.
  rewrite phase1_surface_certified_resolver_proposition_atom_equation in Hresolver.
  destruct input as [| first tail]; try discriminate Hresolver.
  destruct first as [literal | class_name lexeme].
  - unfold proposition_atom_decision in Hresolver.
    simpl in Hresolver.
    destruct (String.eqb literal "(") eqn:Hopen.
    + apply String.eqb_eq in Hopen. subst literal. reflexivity.
    + destruct (String.eqb literal "true") eqn:Htrue.
      * apply String.eqb_eq in Htrue. subst literal. reflexivity.
      * destruct (String.eqb literal "false") eqn:Hfalse.
        -- apply String.eqb_eq in Hfalse. subst literal. reflexivity.
        -- discriminate Hresolver.
  - unfold proposition_atom_decision in Hresolver.
    simpl in Hresolver.
    destruct (String.eqb class_name "IDENTIFIER") eqn:Hclass;
      try discriminate Hresolver.
    apply String.eqb_eq in Hclass.
    subst class_name.
    reflexivity.
Qed.

Lemma phase1_surface_static_argument_resolver_some_trigger :
  forall path input decision,
    phase1_surface_certified_overlap_resolver
      (descend path (AtNonterminal "static_argument")) input = Some decision ->
    continuation_lookahead_mem input static_argument_resolver_trigger = true.
Proof.
  intros path input decision Hresolver.
  rewrite phase1_surface_certified_resolver_static_argument_equation in Hresolver.
  destruct input as [| first tail]; try discriminate Hresolver.
  destruct first as [literal | class_name lexeme].
  - unfold static_argument_decision in Hresolver.
    simpl in Hresolver.
    destruct (String.eqb literal "(") eqn:Hopen.
    + apply String.eqb_eq in Hopen. subst literal. reflexivity.
    + destruct (String.eqb literal "{") eqn:Hbrace.
      * apply String.eqb_eq in Hbrace. subst literal. reflexivity.
      * discriminate Hresolver.
  - discriminate Hresolver.
Qed.

Definition selected_trigger_first_disjointb
  (items : list EbnfExpression)
  (index : nat)
  (trigger : list OverlapToken) : bool :=
  match nth_error items index with
  | Some item =>
      token_intersection_emptyb
        (first_expression
          phase1_surface_nullable_facts
          phase1_surface_first_facts item)
        trigger
  | None => false
  end.

Definition alternative_trigger_coverageb
  (items : list EbnfExpression)
  (interesting : list nat)
  (trigger : list OverlapToken) : bool :=
  forallb
    (fun index =>
      orb
        (nat_memb index interesting)
        (selected_trigger_first_disjointb items index trigger))
    (seq 0 (List.length items)).

Lemma alternative_trigger_coverage_selected :
  forall items interesting trigger index item,
    alternative_trigger_coverageb items interesting trigger = true ->
    nth_error items index = Some item ->
    nat_memb index interesting = true \/
    selected_trigger_first_disjointb items index trigger = true.
Proof.
  intros items interesting trigger index item Hcoverage Hselected.
  unfold alternative_trigger_coverageb in Hcoverage.
  pose proof
    (proj1
      (@forallb_forall nat
        (fun candidate =>
          orb
            (nat_memb candidate interesting)
            (selected_trigger_first_disjointb items candidate trigger))
        (seq 0 (List.length items)))
      Hcoverage) as Hcoverage_all.
  assert (Hlt : index < List.length items).
  {
    apply nth_error_Some.
    rewrite Hselected.
    discriminate.
  }
  assert (Hin : In index (seq 0 (List.length items))).
  {
    apply in_seq.
    lia.
  }
  specialize (Hcoverage_all index Hin).
  apply orb_true_iff in Hcoverage_all.
  exact Hcoverage_all.
Qed.

Lemma selected_trigger_first_disjointb_sound :
  forall items index item trigger,
    selected_trigger_first_disjointb items index trigger = true ->
    nth_error items index = Some item ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts item)
      trigger = [].
Proof.
  intros items index item trigger Hdisjoint Hnth.
  unfold selected_trigger_first_disjointb in Hdisjoint.
  rewrite Hnth in Hdisjoint.
  apply token_intersection_emptyb_sound.
  exact Hdisjoint.
Qed.

Lemma selected_trigger_first_disjointb_excludes_resolver_trigger :
  forall path items index item input rest tree trigger,
    selected_trigger_first_disjointb items index trigger = true ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem input trigger = true ->
    False.
Proof.
  intros path items index item input rest tree trigger
    Hdisjoint Hnth Hderive Hsafe Hnonnullable Htrigger.
  pose proof
    (phase1_surface_nonnullable_derivation_starts_inputb
      (descend path (AtAlternative index)) item input rest tree
      Hderive Hsafe Hnonnullable) as Hstarts.
  pose proof
    (selected_trigger_first_disjointb_sound
      items index item trigger Hdisjoint Hnth) as Hintersection.
  destruct input as [| first tail].
  - rewrite expression_starts_inputb_nil_equation in Hstarts.
    rewrite Hnonnullable in Hstarts.
    discriminate Hstarts.
  - rewrite expression_starts_inputb_cons_equation in Hstarts.
    unfold continuation_lookahead_mem in Htrigger.
    pose proof
      (token_intersection_empty_excludes_shared_member
        (concrete_token_shape first)
        (first_expression
          phase1_surface_nullable_facts
          phase1_surface_first_facts item)
        trigger Hintersection Htrigger) as Hexcluded.
    rewrite Hstarts in Hexcluded.
    discriminate Hexcluded.
Qed.

Lemma alternative_trigger_coverage_forces_interesting :
  forall path items interesting trigger index item input rest tree,
    alternative_trigger_coverageb items interesting trigger = true ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem input trigger = true ->
    In index interesting.
Proof.
  intros path items interesting trigger index item input rest tree
    Hcoverage Hnth Hderive Hsafe Hnonnullable Htrigger.
  destruct
    (alternative_trigger_coverage_selected
      items interesting trigger index item Hcoverage Hnth)
    as [Hinteresting | Hdisjoint].
  - apply resolver_none_nat_memb_true_in.
    exact Hinteresting.
  - exfalso.
    eapply selected_trigger_first_disjointb_excludes_resolver_trigger.
    + exact Hdisjoint.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + exact Htrigger.
Qed.

Definition declaration_resolver_some_indices : list nat := [6; 7].
Definition generic_requirement_resolver_some_indices : list nat := [4; 8].
Definition pattern_resolver_some_indices : list nat := [0; 2].
Definition primary_expression_resolver_some_indices : list nat := [0; 1].
Definition static_argument_resolver_some_indices : list nat := [0; 2; 3].

Theorem phase1_surface_declaration_resolver_some_trigger_coverage :
  alternative_trigger_coverageb
    phase1_surface_resolver_declaration_items
    declaration_resolver_some_indices
    declaration_resolver_trigger = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_generic_requirement_resolver_some_trigger_coverage :
  alternative_trigger_coverageb
    phase1_surface_resolver_generic_requirement_items
    generic_requirement_resolver_some_indices
    generic_requirement_resolver_trigger = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_pattern_resolver_some_trigger_coverage :
  alternative_trigger_coverageb
    phase1_surface_resolver_pattern_items
    pattern_resolver_some_indices
    pattern_resolver_trigger = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_primary_expression_resolver_some_trigger_coverage :
  alternative_trigger_coverageb
    phase1_surface_resolver_primary_expression_items
    primary_expression_resolver_some_indices
    primary_expression_resolver_trigger = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_static_argument_resolver_some_trigger_coverage :
  alternative_trigger_coverageb
    phase1_surface_resolver_static_argument_items
    static_argument_resolver_some_indices
    static_argument_resolver_trigger = true.
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_static_value_cannot_start_brace :
  forall path tail rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "static_value_expression")
      (TLiteral "{" :: tail) rest tree ->
    False.
Proof.
  intros path tail rest tree Hderive.
  pose proof
    (phase1_surface_nonnullable_derivation_starts_inputb
      path
      (ENonterminal "static_value_expression")
      (TLiteral "{" :: tail) rest tree
      Hderive
      phase1_surface_static_value_choice_safe
      phase1_surface_static_value_nonnullable) as Hstarts.
  rewrite expression_starts_inputb_cons_equation in Hstarts.
  vm_compute in Hstarts.
  discriminate Hstarts.
Qed.

Lemma phase1_surface_declaration_resolver_some_oracle_alternative :
  forall path items index item input rest tree decision,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path provider_declaration_suffix = true ->
    lookupRule "declaration" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree decision
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  unfold provider_declaration_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "declaration" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_declaration_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  pose proof
    (phase1_surface_declaration_resolver_some_trigger
      root_prefix input decision Hresolver) as Htrigger.
  pose proof
    (alternative_trigger_coverage_forces_interesting
      (descend root_prefix (AtNonterminal "declaration"))
      phase1_surface_resolver_declaration_items
      declaration_resolver_some_indices declaration_resolver_trigger
      index item input rest tree
      phase1_surface_declaration_resolver_some_trigger_coverage
      Hnth Hderive Hsafe Hnonnullable Htrigger) as Hinteresting.
  unfold declaration_resolver_some_indices in Hinteresting.
  simpl in Hinteresting.
  destruct Hinteresting as [Hindex | [Hindex | Hfalse]].
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_provider_contract_certified_commitment.
    exact Hderive.
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_provider_implementation_certified_commitment.
    exact Hderive.
  - contradiction.
Qed.

Lemma phase1_surface_generic_requirement_resolver_some_oracle_alternative :
  forall path items index item input rest tree decision,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path generic_requirement_suffix = true ->
    lookupRule "generic_requirement" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree decision
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  unfold generic_requirement_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "generic_requirement" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_generic_requirement_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  pose proof
    (phase1_surface_generic_requirement_resolver_some_trigger
      root_prefix input decision Hresolver) as Htrigger.
  pose proof
    (alternative_trigger_coverage_forces_interesting
      (descend root_prefix (AtNonterminal "generic_requirement"))
      phase1_surface_resolver_generic_requirement_items
      generic_requirement_resolver_some_indices generic_requirement_resolver_trigger
      index item input rest tree
      phase1_surface_generic_requirement_resolver_some_trigger_coverage
      Hnth Hderive Hsafe Hnonnullable Htrigger) as Hinteresting.
  unfold generic_requirement_resolver_some_indices in Hinteresting.
  simpl in Hinteresting.
  destruct Hinteresting as [Hindex | [Hindex | Hfalse]].
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_generic_boundary_name_certified_commitment.
    exact Hderive.
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_generic_boundary_representation_certified_commitment.
    exact Hderive.
  - contradiction.
Qed.

Lemma phase1_surface_pattern_resolver_some_oracle_alternative :
  forall path outer_follow items index item input rest tree decision,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path pattern_suffix = true ->
    lookupRule "pattern" phase1_surface_rules = Some (EAlternative items) ->
    outer_follow = lookup_tokens "pattern" phase1_surface_follow_facts ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path outer_follow items index item input rest tree decision
    Hpath Hsuffix Hlookup Hfollow Hresolver Hnth Hderive Hsafe Hnonnullable
    Hcontinuation.
  unfold pattern_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "pattern" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_pattern_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  assert (Hpattern_continuation :
    continuation_lookahead_mem rest phase1_surface_pattern_follow = true).
  {
    unfold phase1_surface_pattern_follow.
    rewrite <- Hfollow.
    exact Hcontinuation.
  }
  pose proof
    (phase1_surface_pattern_resolver_some_trigger
      root_prefix input decision Hresolver) as Htrigger.
  pose proof
    (alternative_trigger_coverage_forces_interesting
      (descend root_prefix (AtNonterminal "pattern"))
      phase1_surface_resolver_pattern_items
      pattern_resolver_some_indices pattern_resolver_trigger
      index item input rest tree
      phase1_surface_pattern_resolver_some_trigger_coverage
      Hnth Hderive Hsafe Hnonnullable Htrigger) as Hinteresting.
  unfold pattern_resolver_some_indices in Hinteresting.
  simpl in Hinteresting.
  destruct Hinteresting as [Hindex | [Hindex | Hfalse]].
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_identifier_pattern_certified_commitment.
    + exact Hderive.
    + exact Hpattern_continuation.
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_record_pattern_certified_commitment.
    exact Hderive.
  - contradiction.
Qed.

Lemma phase1_surface_primary_expression_resolver_some_oracle_alternative :
  forall path items index item input rest tree decision,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path primary_expression_suffix = true ->
    lookupRule "primary_expression" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree decision
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  unfold primary_expression_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "primary_expression" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_primary_expression_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  pose proof
    (phase1_surface_primary_expression_resolver_some_trigger
      root_prefix input decision Hresolver) as Htrigger.
  pose proof
    (alternative_trigger_coverage_forces_interesting
      (descend root_prefix (AtNonterminal "primary_expression"))
      phase1_surface_resolver_primary_expression_items
      primary_expression_resolver_some_indices primary_expression_resolver_trigger
      index item input rest tree
      phase1_surface_primary_expression_resolver_some_trigger_coverage
      Hnth Hderive Hsafe Hnonnullable Htrigger) as Hinteresting.
  unfold primary_expression_resolver_some_indices in Hinteresting.
  simpl in Hinteresting.
  destruct Hinteresting as [Hindex | [Hindex | Hfalse]].
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_tuple_expression_certified_commitment.
    exact Hderive.
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_parenthesized_expression_certified_commitment.
    exact Hderive.
  - contradiction.
Qed.

Lemma phase1_surface_relation_resolver_some_oracle_alternative :
  forall root_prefix path index input rest tree decision,
    path = descend root_prefix (AtNonterminal "proposition_atom") ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index))
      (ENonterminal "relation_proposition") input rest tree ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros root_prefix path index input rest tree decision Hpath Hresolver Hderive.
  subst path.
  assert (Hlocal : proposition_atom_decision input = Some decision).
  {
    rewrite <- phase1_surface_certified_resolver_proposition_atom_equation.
    exact Hresolver.
  }
  destruct input as [| first tail]; try discriminate Hlocal.
  destruct first as [literal | class_name lexeme].
  - unfold proposition_atom_decision in Hlocal.
    simpl in Hlocal.
    destruct (String.eqb literal "(") eqn:Hopen.
    + apply String.eqb_eq in Hopen. subst literal.
      apply predictive_bridge_oracle_from_resolver.
      eapply phase1_surface_relation_parenthesis_certified_commitment.
      * exact Hderive.
      * reflexivity.
    + destruct (String.eqb literal "true") eqn:Htrue.
      * apply String.eqb_eq in Htrue. subst literal.
        apply predictive_bridge_oracle_from_resolver.
        eapply phase1_surface_relation_true_certified_commitment.
        -- exact Hderive.
        -- reflexivity.
      * destruct (String.eqb literal "false") eqn:Hfalse.
        -- apply String.eqb_eq in Hfalse. subst literal.
           apply predictive_bridge_oracle_from_resolver.
           eapply phase1_surface_relation_false_certified_commitment.
           ++ exact Hderive.
           ++ reflexivity.
        -- discriminate Hlocal.
  - unfold proposition_atom_decision in Hlocal.
    simpl in Hlocal.
    destruct (String.eqb class_name "IDENTIFIER") eqn:Hclass;
      try discriminate Hlocal.
    apply String.eqb_eq in Hclass.
    subst class_name.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_relation_identifier_certified_commitment.
    + exact Hderive.
    + reflexivity.
Qed.

Lemma phase1_surface_proposition_atom_resolver_some_oracle_alternative :
  forall path outer_follow items index item input rest tree decision,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path proposition_atom_suffix = true ->
    lookupRule "proposition_atom" phase1_surface_rules = Some (EAlternative items) ->
    outer_follow = lookup_tokens "proposition_atom" phase1_surface_follow_facts ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path outer_follow items index item input rest tree decision
    Hpath Hsuffix Hlookup Hfollow Hresolver Hnth Hderive Hsafe Hnonnullable
    Hcontinuation.
  unfold proposition_atom_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "proposition_atom" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_proposition_atom_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  assert (Hproposition_continuation :
    continuation_lookahead_mem rest phase1_surface_proposition_atom_follow = true).
  {
    Transparent phase1_surface_proposition_atom_follow.
    unfold phase1_surface_proposition_atom_follow.
    rewrite <- Hfollow.
    exact Hcontinuation.
  }
  destruct index as [| [| [| [| [| index]]]]].
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    eapply phase1_surface_relation_resolver_some_oracle_alternative.
    + reflexivity.
    + exact Hresolver.
    + exact Hderive.
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_grouped_proposition_certified_commitment.
    + exact Hderive.
    + exact Hproposition_continuation.
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_true_proposition_certified_commitment.
    + exact Hderive.
    + exact Hproposition_continuation.
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_false_proposition_certified_commitment.
    + exact Hderive.
    + exact Hproposition_continuation.
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_claim_application_certified_commitment.
    + exact Hderive.
    + exact Hproposition_continuation.
  - vm_compute in Hnth.
    discriminate Hnth.
Qed.

Lemma phase1_surface_static_type_resolver_some_oracle_alternative :
  forall root_prefix path index input rest tree decision,
    path = descend root_prefix (AtNonterminal "static_argument") ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index))
      (ENonterminal "nonreference_type_expression") input rest tree ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros root_prefix path index input rest tree decision Hpath Hresolver Hderive.
  subst path.
  assert (Hlocal : static_argument_decision input = Some decision).
  {
    rewrite <- phase1_surface_certified_resolver_static_argument_equation.
    exact Hresolver.
  }
  destruct input as [| first tail]; try discriminate Hlocal.
  destruct first as [literal | class_name lexeme].
  - unfold static_argument_decision in Hlocal.
    simpl in Hlocal.
    destruct (String.eqb literal "(") eqn:Hopen.
    + apply String.eqb_eq in Hopen. subst literal.
      apply predictive_bridge_oracle_from_resolver.
      eapply phase1_surface_static_type_parenthesis_certified_commitment.
      * exact Hderive.
      * reflexivity.
    + destruct (String.eqb literal "{") eqn:Hbrace.
      * apply String.eqb_eq in Hbrace. subst literal.
        apply predictive_bridge_oracle_from_resolver.
        eapply phase1_surface_static_type_brace_certified_commitment.
        -- exact Hderive.
        -- reflexivity.
      * discriminate Hlocal.
  - discriminate Hlocal.
Qed.

Lemma phase1_surface_static_value_resolver_some_oracle_alternative :
  forall root_prefix path index input rest tree decision,
    path = descend root_prefix (AtNonterminal "static_argument") ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index))
      (ENonterminal "static_value_expression") input rest tree ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros root_prefix path index input rest tree decision Hpath Hresolver Hderive.
  subst path.
  assert (Hlocal : static_argument_decision input = Some decision).
  {
    rewrite <- phase1_surface_certified_resolver_static_argument_equation.
    exact Hresolver.
  }
  destruct input as [| first tail]; try discriminate Hlocal.
  destruct first as [literal | class_name lexeme].
  - unfold static_argument_decision in Hlocal.
    simpl in Hlocal.
    destruct (String.eqb literal "(") eqn:Hopen.
    + apply String.eqb_eq in Hopen. subst literal.
      apply predictive_bridge_oracle_from_resolver.
      eapply phase1_surface_static_value_parenthesis_certified_commitment.
      * exact Hderive.
      * reflexivity.
    + destruct (String.eqb literal "{") eqn:Hbrace.
      * apply String.eqb_eq in Hbrace. subst literal.
        exfalso.
        eapply phase1_surface_static_value_cannot_start_brace.
        exact Hderive.
      * discriminate Hlocal.
  - discriminate Hlocal.
Qed.

Lemma phase1_surface_static_argument_resolver_some_oracle_alternative :
  forall path items index item input rest tree decision,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path static_argument_suffix = true ->
    lookupRule "static_argument" phase1_surface_rules = Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree decision
    Hpath Hsuffix Hlookup Hresolver Hnth Hderive Hsafe Hnonnullable.
  pose proof Hsuffix as Hsuffix_original.
  unfold static_argument_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape path "static_argument" Hsuffix)
    as [root_prefix Hshape].
  subst path.
  rewrite phase1_surface_resolver_static_argument_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  pose proof
    (phase1_surface_static_argument_resolver_some_trigger
      root_prefix input decision Hresolver) as Htrigger.
  pose proof
    (alternative_trigger_coverage_forces_interesting
      (descend root_prefix (AtNonterminal "static_argument"))
      phase1_surface_resolver_static_argument_items
      static_argument_resolver_some_indices static_argument_resolver_trigger
      index item input rest tree
      phase1_surface_static_argument_resolver_some_trigger_coverage
      Hnth Hderive Hsafe Hnonnullable Htrigger) as Hinteresting.
  unfold static_argument_resolver_some_indices in Hinteresting.
  simpl in Hinteresting.
  destruct Hinteresting as [Hindex | [Hindex | [Hindex | Hfalse]]].
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    eapply phase1_surface_static_type_resolver_some_oracle_alternative.
    + reflexivity.
    + exact Hresolver.
    + exact Hderive.
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    eapply phase1_surface_static_value_resolver_some_oracle_alternative.
    + reflexivity.
    + exact Hresolver.
    + exact Hderive.
  - subst index.
    vm_compute in Hnth.
    inversion Hnth; subst item.
    apply predictive_bridge_oracle_from_resolver.
    eapply phase1_surface_effect_set_certified_commitment.
    exact Hderive.
  - contradiction.
Qed.

Theorem phase1_surface_resolver_some_oracle_alternative :
  forall path outer_follow items index item input rest tree decision,
    phase1_surface_expression_path_context path (EAlternative items) ->
    alternative_resolver_contextb path outer_follow = true ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index)) item input rest tree ->
    choice_bodies_nonnullable_fuel expression_fuel item = true ->
    nullable_expression phase1_surface_nullable_facts item = false ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle path input = Some (ChooseAlternative index).
Proof.
  intros path outer_follow items index item input rest tree decision
    Hpath Hresolver_context Hresolver Hnth Hderive Hsafe Hnonnullable
    Hcontinuation.
  pose proof
    (phase1_surface_alternative_resolver_root_classified
      path outer_follow items Hpath Hresolver_context) as Hroot.
  destruct Hroot as
    [Hsuffix Hlookup
    | Hsuffix Hlookup
    | Hsuffix Hlookup Hfollow
    | Hsuffix Hlookup
    | Hsuffix Hlookup Hfollow
    | Hsuffix Hlookup].
  - eapply phase1_surface_declaration_resolver_some_oracle_alternative.
    + exact Hpath.
    + exact Hsuffix.
    + exact Hlookup.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
  - eapply phase1_surface_generic_requirement_resolver_some_oracle_alternative.
    + exact Hpath.
    + exact Hsuffix.
    + exact Hlookup.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
  - eapply phase1_surface_pattern_resolver_some_oracle_alternative.
    + exact Hpath.
    + exact Hsuffix.
    + exact Hlookup.
    + exact Hfollow.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + exact Hcontinuation.
  - eapply phase1_surface_primary_expression_resolver_some_oracle_alternative.
    + exact Hpath.
    + exact Hsuffix.
    + exact Hlookup.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
  - eapply phase1_surface_proposition_atom_resolver_some_oracle_alternative.
    + exact Hpath.
    + exact Hsuffix.
    + exact Hlookup.
    + exact Hfollow.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
    + exact Hcontinuation.
  - eapply phase1_surface_static_argument_resolver_some_oracle_alternative.
    + exact Hpath.
    + exact Hsuffix.
    + exact Hlookup.
    + exact Hresolver.
    + exact Hnth.
    + exact Hderive.
    + exact Hsafe.
    + exact Hnonnullable.
Qed.
