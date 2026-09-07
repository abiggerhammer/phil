From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyPathSuffixReflection
  GrammarDeterminacyAlternativeResolverContext
  GrammarDeterminacyAlternativeTrailingCommaExclusion.

Import ListNotations.
Open Scope string_scope.

(*
  Resolver exclusion facts for the final ordinary-derivation ->
  predictive-oracle mutual induction.

  The fallback optional branch needs to know that no certified overlap
  resolver can fire at an optional expression.  Likewise, the ordinary
  repetition fallback applies only away from the five trailing-comma resolver
  sites.  Package those two exclusions here from the exact generated paths.
*)

Lemma case_pattern_comma_repeat_suffix_is_repetition :
  forall prefix expression,
    phase1_surface_expression_path_context
      (List.app prefix case_pattern_comma_repeat_suffix)
      expression ->
    exists body,
      expression = ERepetition body.
Proof.
  intros prefix expression Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - unfold case_pattern_comma_repeat_suffix in Hpath.
    apply expression_at_path_nonterminal_head_inv in Hpath.
    destruct Hpath as [body [Hmiddle_shape [Hlookup Htail]]].
    subst middle.
    vm_compute in Hlookup.
    inversion Hlookup.
    subst body.
    vm_compute in Htail.
    inversion Htail.
    eexists.
    reflexivity.
  - discriminate Hpath.
Qed.

Lemma construct_expression_comma_repeat_suffix_is_repetition :
  forall prefix expression,
    phase1_surface_expression_path_context
      (List.app prefix construct_expression_comma_repeat_suffix)
      expression ->
    exists body,
      expression = ERepetition body.
Proof.
  intros prefix expression Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - unfold construct_expression_comma_repeat_suffix in Hpath.
    apply expression_at_path_nonterminal_head_inv in Hpath.
    destruct Hpath as [body [Hmiddle_shape [Hlookup Htail]]].
    subst middle.
    vm_compute in Hlookup.
    inversion Hlookup.
    subst body.
    vm_compute in Htail.
    inversion Htail.
    eexists.
    reflexivity.
  - discriminate Hpath.
Qed.

Lemma record_decl_comma_repeat_suffix_is_repetition :
  forall prefix expression,
    phase1_surface_expression_path_context
      (List.app prefix record_decl_comma_repeat_suffix)
      expression ->
    exists body,
      expression = ERepetition body.
Proof.
  intros prefix expression Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - unfold record_decl_comma_repeat_suffix in Hpath.
    apply expression_at_path_nonterminal_head_inv in Hpath.
    destruct Hpath as [body [Hmiddle_shape [Hlookup Htail]]].
    subst middle.
    vm_compute in Hlookup.
    inversion Hlookup.
    subst body.
    vm_compute in Htail.
    inversion Htail.
    eexists.
    reflexivity.
  - discriminate Hpath.
Qed.

Lemma record_pattern_comma_repeat_suffix_is_repetition :
  forall prefix expression,
    phase1_surface_expression_path_context
      (List.app prefix record_pattern_comma_repeat_suffix)
      expression ->
    exists body,
      expression = ERepetition body.
Proof.
  intros prefix expression Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - unfold record_pattern_comma_repeat_suffix in Hpath.
    apply expression_at_path_nonterminal_head_inv in Hpath.
    destruct Hpath as [body [Hmiddle_shape [Hlookup Htail]]].
    subst middle.
    vm_compute in Hlookup.
    inversion Hlookup.
    subst body.
    vm_compute in Htail.
    inversion Htail.
    eexists.
    reflexivity.
  - discriminate Hpath.
Qed.

Lemma variant_payload_comma_repeat_suffix_is_repetition :
  forall prefix expression,
    phase1_surface_expression_path_context
      (List.app prefix variant_payload_comma_repeat_suffix)
      expression ->
    exists body,
      expression = ERepetition body.
Proof.
  intros prefix expression Hpath.
  unfold phase1_surface_expression_path_context,
    phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hmiddle.
  - unfold variant_payload_comma_repeat_suffix in Hpath.
    apply expression_at_path_nonterminal_head_inv in Hpath.
    destruct Hpath as [body [Hmiddle_shape [Hlookup Htail]]].
    subst middle.
    vm_compute in Hlookup.
    inversion Hlookup.
    subst body.
    vm_compute in Htail.
    inversion Htail.
    eexists.
    reflexivity.
  - discriminate Hpath.
Qed.

Theorem phase1_surface_trailing_comma_path_expression_is_repetition :
  forall path expression,
    phase1_surface_expression_path_context path expression ->
    trailing_comma_repeat_pathb path = true ->
    exists body,
      expression = ERepetition body.
Proof.
  intros path expression Hpath Htrail.
  unfold trailing_comma_repeat_pathb in Htrail.
  apply orb_true_iff in Htrail.
  destruct Htrail as [Hcase | Hrest].
  - apply path_has_suffixb_true_shape in Hcase.
    destruct Hcase as [prefix Hshape].
    subst path.
    eapply case_pattern_comma_repeat_suffix_is_repetition.
    exact Hpath.
  - apply orb_true_iff in Hrest.
    destruct Hrest as [Hconstruct | Hrest].
    + apply path_has_suffixb_true_shape in Hconstruct.
      destruct Hconstruct as [prefix Hshape].
      subst path.
      eapply construct_expression_comma_repeat_suffix_is_repetition.
      exact Hpath.
    + apply orb_true_iff in Hrest.
      destruct Hrest as [Hrecord_decl | Hrest].
      * apply path_has_suffixb_true_shape in Hrecord_decl.
        destruct Hrecord_decl as [prefix Hshape].
        subst path.
        eapply record_decl_comma_repeat_suffix_is_repetition.
        exact Hpath.
      * apply orb_true_iff in Hrest.
        destruct Hrest as [Hrecord_pattern | Hvariant].
        -- apply path_has_suffixb_true_shape in Hrecord_pattern.
           destruct Hrecord_pattern as [prefix Hshape].
           subst path.
           eapply record_pattern_comma_repeat_suffix_is_repetition.
           exact Hpath.
        -- apply path_has_suffixb_true_shape in Hvariant.
           destruct Hvariant as [prefix Hshape].
           subst path.
           eapply variant_payload_comma_repeat_suffix_is_repetition.
           exact Hpath.
Qed.

Theorem phase1_surface_optional_excludes_trailing_comma_path :
  forall path body,
    phase1_surface_expression_path_context path (EOptional body) ->
    trailing_comma_repeat_pathb path = false.
Proof.
  intros path body Hpath.
  destruct (trailing_comma_repeat_pathb path) eqn:Htrail.
  - exfalso.
    destruct
      (phase1_surface_trailing_comma_path_expression_is_repetition
        path (EOptional body) Hpath Htrail)
      as [repetition_body Hshape].
    discriminate Hshape.
  - reflexivity.
Qed.

Theorem phase1_surface_nontrailing_resolver_some_implies_alternative :
  forall path expression input decision,
    phase1_surface_expression_path_context path expression ->
    trailing_comma_repeat_pathb path = false ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    exists items,
      expression = EAlternative items.
Proof.
  intros path expression input decision Hpath Htrail Hresolver.
  unfold phase1_surface_expression_path_context in Hpath.
  unfold phase1_surface_certified_overlap_resolver in Hresolver.
  unfold phase1_surface_simple_resolver in Hresolver.
  destruct
    (path_has_suffixb path provider_declaration_suffix)
    eqn:Hprovider.
  - assert
      (Hlookup : lookupRule "declaration" phase1_surface_rules =
        Some expression).
    {
      eapply phase1_surface_single_nonterminal_suffix_lookup.
      - unfold provider_declaration_suffix in Hprovider.
        exact Hprovider.
      - exact Hpath.
    }
    vm_compute in Hlookup.
    inversion Hlookup.
    eexists.
    reflexivity.
  - destruct
      (path_has_suffixb path generic_requirement_suffix)
      eqn:Hgeneric.
    + assert
        (Hlookup : lookupRule "generic_requirement" phase1_surface_rules =
          Some expression).
      {
        eapply phase1_surface_single_nonterminal_suffix_lookup.
        - unfold generic_requirement_suffix in Hgeneric.
          exact Hgeneric.
        - exact Hpath.
      }
      vm_compute in Hlookup.
      inversion Hlookup.
      eexists.
      reflexivity.
    + rewrite Htrail in Hresolver.
      unfold phase1_surface_structural_resolver in Hresolver.
      destruct (path_has_suffixb path pattern_suffix) eqn:Hpattern.
      * assert
          (Hlookup : lookupRule "pattern" phase1_surface_rules =
            Some expression).
        {
          eapply phase1_surface_single_nonterminal_suffix_lookup.
          - unfold pattern_suffix in Hpattern.
            exact Hpattern.
          - exact Hpath.
        }
        vm_compute in Hlookup.
        inversion Hlookup.
        eexists.
        reflexivity.
      * destruct
          (path_has_suffixb path primary_expression_suffix)
          eqn:Hprimary.
        -- assert
            (Hlookup : lookupRule "primary_expression" phase1_surface_rules =
              Some expression).
           {
             eapply phase1_surface_single_nonterminal_suffix_lookup.
             - unfold primary_expression_suffix in Hprimary.
               exact Hprimary.
             - exact Hpath.
           }
           vm_compute in Hlookup.
           inversion Hlookup.
           eexists.
           reflexivity.
        -- destruct
            (path_has_suffixb path proposition_atom_suffix)
            eqn:Hproposition.
           ++ assert
                (Hlookup : lookupRule "proposition_atom" phase1_surface_rules =
                  Some expression).
              {
                eapply phase1_surface_single_nonterminal_suffix_lookup.
                - unfold proposition_atom_suffix in Hproposition.
                  exact Hproposition.
                - exact Hpath.
              }
              vm_compute in Hlookup.
              inversion Hlookup.
              eexists.
              reflexivity.
           ++ destruct
                (path_has_suffixb path static_argument_suffix)
                eqn:Hstatic.
              ** assert
                   (Hlookup : lookupRule "static_argument" phase1_surface_rules =
                     Some expression).
                 {
                   eapply phase1_surface_single_nonterminal_suffix_lookup.
                   - unfold static_argument_suffix in Hstatic.
                     exact Hstatic.
                   - exact Hpath.
                 }
                 vm_compute in Hlookup.
                 inversion Hlookup.
                 eexists.
                 reflexivity.
              ** discriminate Hresolver.
Qed.

Theorem phase1_surface_nonalternative_nontrailing_resolver_none :
  forall path expression input,
    phase1_surface_expression_path_context path expression ->
    (forall items, expression <> EAlternative items) ->
    trailing_comma_repeat_pathb path = false ->
    phase1_surface_certified_overlap_resolver path input = None.
Proof.
  intros path expression input Hpath Hnonalternative Htrail.
  destruct
    (phase1_surface_certified_overlap_resolver path input)
    as [decision |] eqn:Hresolver.
  - exfalso.
    destruct
      (phase1_surface_nontrailing_resolver_some_implies_alternative
        path expression input decision Hpath Htrail Hresolver)
      as [items Hshape].
    exact (Hnonalternative items Hshape).
  - reflexivity.
Qed.

Corollary phase1_surface_optional_resolver_none :
  forall path body input,
    phase1_surface_expression_path_context path (EOptional body) ->
    phase1_surface_certified_overlap_resolver path input = None.
Proof.
  intros path body input Hpath.
  eapply phase1_surface_nonalternative_nontrailing_resolver_none.
  - exact Hpath.
  - intros items Hshape.
    discriminate Hshape.
  - apply phase1_surface_optional_excludes_trailing_comma_path.
    exact Hpath.
Qed.

Corollary phase1_surface_nontrailing_repetition_resolver_none :
  forall path body input,
    phase1_surface_expression_path_context path (ERepetition body) ->
    trailing_comma_repeat_pathb path = false ->
    phase1_surface_certified_overlap_resolver path input = None.
Proof.
  intros path body input Hpath Htrail.
  eapply phase1_surface_nonalternative_nontrailing_resolver_none.
  - exact Hpath.
  - intros items Hshape.
    discriminate Hshape.
  - exact Htrail.
Qed.
