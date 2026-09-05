From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyFollowCoverage
  GrammarDeterminacyPredictiveFallbackSoundness
  GrammarDeterminacyAlternativeEarlierDisjoint
  GrammarDeterminacyAlternativeResolverContext
  GrammarDeterminacyAlternativeResolverNoneSemantic
  GrammarDeterminacyPredictiveConversion.

Import ListNotations.
Open Scope string_scope.

(*
  Close the one input-sensitive residue left by the resolver-None semantic
  package: static_argument branch 2, static_value_expression.

  Branch 2 is not globally FIRST-disjoint from its predecessors because
  nonreference_type_expression and static_value_expression can both begin with
  "(".  The exact generated FIRST intersection is nevertheless just that one
  token.  If the certified resolver returns None, #760 already rules out an
  ordinary static-value derivation beginning with "(".  Therefore branch 0 is
  rejected on the actual input; branch 1 is globally FIRST-disjoint.  This is
  exactly the earlier-branch fact needed by predictive fallback.
*)

Lemma token_mem_true_of_in :
  forall token tokens,
    In token tokens ->
    token_mem token tokens = true.
Proof.
  intros token tokens Hin.
  induction tokens as [| head tail IH].
  - contradiction.
  - simpl in Hin.
    simpl.
    destruct Hin as [Heq | Hin].
    + subst head.
      rewrite overlap_token_eqb_refl.
      reflexivity.
    + destruct (overlap_token_eqb token head) eqn:Heq.
      * reflexivity.
      * apply IH.
        exact Hin.
Qed.

Lemma token_intersection_shared_in :
  forall token left right,
    token_mem token left = true ->
    token_mem token right = true ->
    In token (token_intersection left right).
Proof.
  intros token left right Hleft Hright.
  apply follow_token_mem_true_in in Hleft.
  induction left as [| head tail IH].
  - contradiction.
  - simpl in Hleft.
    simpl.
    destruct Hleft as [Heq | Hin].
    + subst head.
      rewrite Hright.
      left. reflexivity.
    + destruct (token_mem head right) eqn:Hhead.
      * right.
        apply IH.
        exact Hin.
      * apply IH.
        exact Hin.
Qed.

Lemma phase1_surface_static_argument_branch_zero_exact :
  nth_error phase1_surface_resolver_static_argument_items 0 =
    Some (ENonterminal "nonreference_type_expression").
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_static_argument_branch_one_exact :
  nth_error phase1_surface_resolver_static_argument_items 1 =
    Some (ENonterminal "nonreference_session_expression").
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_static_argument_branch_two_exact :
  nth_error phase1_surface_resolver_static_argument_items 2 =
    Some (ENonterminal "static_value_expression").
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_static_type_value_first_intersection_exact :
  token_intersection
    (first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      (ENonterminal "nonreference_type_expression"))
    (first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      (ENonterminal "static_value_expression")) =
  [OverlapLiteral "("].
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_static_session_value_first_disjoint :
  token_intersection
    (first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      (ENonterminal "nonreference_session_expression"))
    (first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      (ENonterminal "static_value_expression")) = [].
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_static_value_choice_safe :
  choice_bodies_nonnullable_fuel
    expression_fuel
    (ENonterminal "static_value_expression") = true.
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_static_value_nonnullable :
  nullable_expression
    phase1_surface_nullable_facts
    (ENonterminal "static_value_expression") = false.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_static_value_resolver_none_excludes_earlier :
  forall path items input rest tree,
    path_has_suffixb path static_argument_suffix = true ->
    lookupRule "static_argument" phase1_surface_rules =
      Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = None ->
    Derives phase1_surface_rules
      (descend path (AtAlternative 2))
      (ENonterminal "static_value_expression") input rest tree ->
    forall earlier_index earlier_item,
      earlier_index < 2 ->
      nth_error items earlier_index = Some earlier_item ->
      expression_starts_inputb earlier_item input = false.
Proof.
  intros path items input rest tree Hsuffix Hlookup Hresolver Hderive.
  unfold static_argument_suffix in Hsuffix.
  destruct
    (path_has_single_nonterminal_suffix_shape
      path "static_argument" Hsuffix)
    as [root_prefix Hpath].
  subst path.
  rewrite phase1_surface_resolver_static_argument_lookup_exact in Hlookup.
  inversion Hlookup; subst items.
  pose proof
    (phase1_surface_nonnullable_derivation_starts_inputb
      (descend
        (descend root_prefix (AtNonterminal "static_argument"))
        (AtAlternative 2))
      (ENonterminal "static_value_expression")
      input rest tree Hderive
      phase1_surface_static_value_choice_safe
      phase1_surface_static_value_nonnullable)
    as Hselected.
  intros earlier_index earlier_item Hlt Hearlier.
  destruct earlier_index as [| [| earlier_index]].
  - rewrite phase1_surface_static_argument_branch_zero_exact in Hearlier.
    inversion Hearlier; subst earlier_item.
    destruct input as [| first_token tail].
    + rewrite expression_starts_inputb_nil_equation in Hselected.
      rewrite phase1_surface_static_value_nonnullable in Hselected.
      discriminate Hselected.
    + rewrite expression_starts_inputb_cons_equation in Hselected.
      rewrite expression_starts_inputb_cons_equation.
      destruct
        (token_mem
          (concrete_token_shape first_token)
          (first_expression
            phase1_surface_nullable_facts
            phase1_surface_first_facts
            (ENonterminal "nonreference_type_expression")))
        eqn:Htype.
      * exfalso.
        pose proof
          (token_intersection_shared_in
            (concrete_token_shape first_token)
            (first_expression
              phase1_surface_nullable_facts
              phase1_surface_first_facts
              (ENonterminal "nonreference_type_expression"))
            (first_expression
              phase1_surface_nullable_facts
              phase1_surface_first_facts
              (ENonterminal "static_value_expression"))
            Htype Hselected)
          as Hintersection.
        rewrite
          phase1_surface_static_type_value_first_intersection_exact
          in Hintersection.
        simpl in Hintersection.
        destruct Hintersection as [Hshape | Hfalse].
        -- assert (Hinput :
             first_token :: tail = TLiteral "(" :: tail).
           {
             destruct first_token as [literal | class_name lexeme].
             - simpl in Hshape.
               inversion Hshape; subst literal.
               reflexivity.
             - discriminate Hshape.
           }
           eapply phase1_surface_static_value_parenthesis_resolver_none_impossible.
           ++ exact Hderive.
           ++ exact Hinput.
           ++ exact Hresolver.
        -- contradiction.
      * reflexivity.
  - rewrite phase1_surface_static_argument_branch_one_exact in Hearlier.
    inversion Hearlier; subst earlier_item.
    destruct input as [| first_token tail].
    + rewrite expression_starts_inputb_nil_equation in Hselected.
      rewrite phase1_surface_static_value_nonnullable in Hselected.
      discriminate Hselected.
    + rewrite expression_starts_inputb_cons_equation in Hselected.
      rewrite expression_starts_inputb_cons_equation.
      eapply token_intersection_empty_excludes_shared_member.
      * exact phase1_surface_static_session_value_first_disjoint.
      * exact Hselected.
  - lia.
Qed.

Theorem phase1_surface_static_value_resolver_none_fallback :
  forall path items input rest tree,
    path_has_suffixb path static_argument_suffix = true ->
    lookupRule "static_argument" phase1_surface_rules =
      Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = None ->
    Derives phase1_surface_rules
      (descend path (AtAlternative 2))
      (ENonterminal "static_value_expression") input rest tree ->
    predictive_fallback_decision (EAlternative items) input =
      Some (ChooseAlternative 2).
Proof.
  intros path items input rest tree Hsuffix Hlookup Hresolver Hderive.
  assert (Hlookup_copy := Hlookup).
  rewrite phase1_surface_resolver_static_argument_lookup_exact in Hlookup_copy.
  inversion Hlookup_copy; subst items.
  eapply predictive_fallback_alternative_from_derivation.
  - exact phase1_surface_static_argument_branch_two_exact.
  - exact Hderive.
  - exact phase1_surface_static_value_choice_safe.
  - exact phase1_surface_static_value_nonnullable.
  - intros earlier_index earlier_item Hlt Hearlier.
    eapply phase1_surface_static_value_resolver_none_excludes_earlier.
    + exact Hsuffix.
    + exact phase1_surface_resolver_static_argument_lookup_exact.
    + exact Hresolver.
    + exact Hderive.
    + exact Hlt.
    + exact Hearlier.
Qed.

Theorem phase1_surface_static_value_resolver_none_oracle :
  forall path items input rest tree,
    phase1_surface_expression_path_context path (EAlternative items) ->
    path_has_suffixb path static_argument_suffix = true ->
    lookupRule "static_argument" phase1_surface_rules =
      Some (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = None ->
    Derives phase1_surface_rules
      (descend path (AtAlternative 2))
      (ENonterminal "static_value_expression") input rest tree ->
    phase1_surface_predictive_oracle path input =
      Some (ChooseAlternative 2).
Proof.
  intros path items input rest tree Hpath Hsuffix Hlookup Hresolver Hderive.
  eapply predictive_bridge_oracle_from_fallback.
  - exact Hresolver.
  - exact Hpath.
  - eapply phase1_surface_static_value_resolver_none_fallback; eauto.
Qed.
