From Stdlib Require Import Bool.Bool Lists.List Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyFollowCoverage
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection
  GrammarDeterminacyPredictiveBridge
  GrammarDeterminacyActualCanonicalPath
  GrammarDeterminacyActualCanonicalAlternativeTotal
  GrammarDeterminacyResolverFollowCompatibility
  GrammarDeterminacyRootedTrailingCommaInvariance
  GrammarDeterminacyCompleteNonterminalReset
  GrammarDeterminacySequenceHeadTrailingContext
  GrammarDeterminacyTrailingCommaConversion
  GrammarDeterminacyTrailingCommaOracleLift
  GrammarDeterminacyStructuralChoiceConversion.

Import ListNotations.

Definition phase1_surface_expression_stop_condition
  (path : SyntaxPath)
  (expression : EbnfExpression)
  (rest : list ConcreteToken) : Prop :=
  match expression with
  | ERepetition _ =>
      phase1_surface_predictive_oracle path rest =
        Some ChooseRepetitionStop
  | _ => True
  end.

Lemma phase1_surface_rule_local_path_nonempty :
  forall path,
    phase1_surface_rule_local_path path ->
    path <> [].
Proof.
  intros path Hlocal.
  destruct Hlocal as [name [tail [Hshape _]]].
  subst path.
  discriminate.
Qed.

Lemma phase1_surface_trailing_comma_nonsequence_descend_false :
  forall path step,
    (match step with
     | AtSequence _ => False
     | _ => True
     end) ->
    trailing_comma_repeat_pathb (descend path step) = false.
Proof.
  intros path step Hstep.
  destruct step as [name | index | index | |];
    try contradiction;
    unfold trailing_comma_repeat_pathb,
      case_pattern_comma_repeat_suffix,
      construct_expression_comma_repeat_suffix,
      record_decl_comma_repeat_suffix,
      record_pattern_comma_repeat_suffix,
      variant_payload_comma_repeat_suffix,
      path_has_suffixb, descend;
    rewrite !List.rev_app_distr;
    simpl;
    reflexivity.
Qed.

Lemma phase1_surface_sequence_choice_safe_for_continuation :
  forall items,
    choice_bodies_nonnullable_fuel
      expression_fuel (ESequence items) = true ->
    forallb (choice_bodies_nonnullable_fuel 255) items = true.
Proof.
  intros items Hsafe.
  unfold expression_fuel in Hsafe.
  simpl in Hsafe.
  exact Hsafe.
Qed.

Lemma phase1_surface_choice_safe_sequence_cons_fixed :
  forall item rest,
    choice_bodies_nonnullable_fuel
      expression_fuel (ESequence (item :: rest)) = true ->
    choice_bodies_nonnullable_fuel expression_fuel item = true /\
    choice_bodies_nonnullable_fuel
      expression_fuel (ESequence rest) = true.
Proof.
  intros item rest Hsafe.
  exact
    (predictive_bridge_choice_safe_sequence_cons_same_fuel
      255 item rest Hsafe).
Qed.

Lemma phase1_surface_choice_safe_alternative_member_fixed :
  forall items index item,
    choice_bodies_nonnullable_fuel
      expression_fuel (EAlternative items) = true ->
    nth_error items index = Some item ->
    nullable_expression phase1_surface_nullable_facts item = false /\
    choice_bodies_nonnullable_fuel expression_fuel item = true.
Proof.
  intros items index item Hsafe Hnth.
  exact
    (predictive_bridge_choice_safe_alternative_member_same_fuel
      255 items index item Hsafe Hnth).
Qed.

Lemma phase1_surface_choice_safe_optional_body_fixed :
  forall body,
    choice_bodies_nonnullable_fuel
      expression_fuel (EOptional body) = true ->
    nullable_expression phase1_surface_nullable_facts body = false /\
    choice_bodies_nonnullable_fuel expression_fuel body = true.
Proof.
  intros body Hsafe.
  exact
    (predictive_bridge_choice_safe_optional_body_same_fuel
      255 body Hsafe).
Qed.

Lemma phase1_surface_choice_safe_repetition_body_fixed :
  forall body,
    choice_bodies_nonnullable_fuel
      expression_fuel (ERepetition body) = true ->
    nullable_expression phase1_surface_nullable_facts body = false /\
    choice_bodies_nonnullable_fuel expression_fuel body = true.
Proof.
  intros body Hsafe.
  exact
    (predictive_bridge_choice_safe_repetition_body_same_fuel
      255 body Hsafe).
Qed.

Lemma phase1_surface_nontrailing_repetition_stop_fixed :
  forall assembly_fuel actual caller_prefix canonical body input outer_follow,
    phase1_surface_actual_canonical_path actual caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    phase1_surface_expression_path_context actual (ERepetition body) ->
    choice_bodies_nonnullable_fuel
      expression_fuel (ERepetition body) = true ->
    oracle_assembly_coverage_fuel
      assembly_fuel canonical outer_follow (ERepetition body) = true ->
    trailing_comma_repeat_pathb canonical = false ->
    continuation_lookahead_mem input outer_follow = true ->
    phase1_surface_predictive_oracle actual input =
      Some ChooseRepetitionStop.
Proof.
  intros assembly_fuel actual caller_prefix canonical body input outer_follow
    Hpath Hlocal Hcontext Hsafe Hassembly Htrail Hcontinuation.
  destruct assembly_fuel as [| assembly_fuel].
  - discriminate Hassembly.
  - eapply phase1_surface_nontrailing_repetition_stop_oracle
      with (choice_fuel := 255) (assembly_fuel := assembly_fuel)
           (caller_prefix := caller_prefix)
           (canonical := canonical) (outer_follow := outer_follow).
    + exact Hpath.
    + exact Hlocal.
    + exact Hcontext.
    + exact Hsafe.
    + unfold expression_fuel. lia.
    + exact Hassembly.
    + exact Htrail.
    + exact Hcontinuation.
Qed.

Definition Phase1PredictiveExpressionProperty
  (path : SyntaxPath)
  (expression : EbnfExpression)
  (input rest : list ConcreteToken)
  (tree : ParseTree) : Prop :=
  forall follow_fuel assembly_fuel caller_prefix canonical outer_follow,
    phase1_surface_actual_canonical_path path caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    phase1_surface_resolver_follow_compatible canonical outer_follow ->
    phase1_surface_expression_path_context path expression ->
    choice_bodies_nonnullable_fuel expression_fuel expression = true ->
    follow_coverage_fuel follow_fuel outer_follow expression = true ->
    oracle_assembly_coverage_fuel
      assembly_fuel canonical outer_follow expression = true ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_expression_stop_condition path expression rest ->
    OracleDerives
      phase1_surface_predictive_oracle phase1_surface_rules
      (GoalExpression path expression)
      input rest (ResultTree tree).

Definition Phase1PredictiveSequenceProperty
  (path : SyntaxPath)
  (index : nat)
  (items : list EbnfExpression)
  (input rest : list ConcreteToken)
  (trees : list ParseTree) : Prop :=
  forall follow_fuel assembly_fuel caller_prefix canonical outer_follow,
    phase1_surface_actual_canonical_path path caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    phase1_surface_sequence_path_context path index items ->
    choice_bodies_nonnullable_fuel
      expression_fuel (ESequence items) = true ->
    follow_coverage_fuel
      follow_fuel outer_follow (ESequence items) = true ->
    oracle_assembly_sequence_coverage_fuel
      assembly_fuel canonical outer_follow index items = true ->
    continuation_lookahead_mem rest outer_follow = true ->
    OracleDerives
      phase1_surface_predictive_oracle phase1_surface_rules
      (GoalSequence path index items)
      input rest (ResultTrees trees).

Definition Phase1PredictiveRepetitionProperty
  (path : SyntaxPath)
  (body : EbnfExpression)
  (input rest : list ConcreteToken)
  (trees : list ParseTree) : Prop :=
  forall follow_fuel assembly_fuel caller_prefix canonical outer_follow,
    phase1_surface_actual_canonical_path path caller_prefix canonical ->
    phase1_surface_rule_local_path canonical ->
    phase1_surface_expression_path_context path (ERepetition body) ->
    choice_bodies_nonnullable_fuel
      expression_fuel (ERepetition body) = true ->
    follow_coverage_fuel
      follow_fuel outer_follow (ERepetition body) = true ->
    oracle_assembly_coverage_fuel
      assembly_fuel canonical outer_follow (ERepetition body) = true ->
    continuation_lookahead_mem rest outer_follow = true ->
    phase1_surface_predictive_oracle path rest =
      Some ChooseRepetitionStop ->
    OracleDerives
      phase1_surface_predictive_oracle phase1_surface_rules
      (GoalRepetition path body)
      input rest (ResultTrees trees).

Theorem phase1_surface_rule_local_derivation_predictive :
  (forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    Phase1PredictiveExpressionProperty path expression input rest tree) /\
  (forall path index items input rest trees,
    DerivesSequence phase1_surface_rules path index items input rest trees ->
    Phase1PredictiveSequenceProperty path index items input rest trees) /\
  (forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    Phase1PredictiveRepetitionProperty path body input rest trees).
Proof.
  apply Derivation_mutind.
  - intros path literal tail.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hresolver Hcontext Hsafe Hfollow Hassembly
      Hcontinuation Hstop.
    constructor.
  - intros path class lexeme tail.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hresolver Hcontext Hsafe Hfollow Hassembly
      Hcontinuation Hstop.
    constructor.
  - intros path name body input rest tree Hlookup Hderive IH.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hresolver Hcontext Hsafe Hfollow Hassembly
      Hcontinuation Hstop.
    destruct follow_fuel as [| follow_fuel].
    + discriminate Hfollow.
    + destruct
        (phase1_surface_complete_nonterminal_reset_invariants
          follow_fuel path outer_follow name body rest
          Hcontext Hlookup Hfollow Hcontinuation)
        as [Hchild_actual
          [Hchild_local
            [Hchild_resolver
              [Hchild_context
                [Hchild_safe
                  [Hchild_follow
                    [Hchild_assembly
                      [Hchild_continuation Hresolver_equation]]]]]]]].
      assert (Hchild_stop :
        phase1_surface_expression_stop_condition
          (descend path (AtNonterminal name)) body rest).
      {
        destruct body as
          [literal | class_name | child_name | items | items |
           child_body | repetition_body]; simpl; try exact I.
        eapply phase1_surface_nontrailing_repetition_stop_fixed
          with (assembly_fuel := oracle_assembly_fuel)
               (caller_prefix := path)
               (canonical := [AtNonterminal name])
               (outer_follow := lookup_tokens name phase1_surface_follow_facts).
        - exact Hchild_actual.
        - exact Hchild_local.
        - exact Hchild_context.
        - exact Hchild_safe.
        - exact Hchild_assembly.
        - apply phase1_surface_trailing_comma_nonsequence_descend_false
            with (path := []).
          simpl. exact I.
        - exact Hchild_continuation.
      }
      apply oracle_nonterminal with body.
      * exact Hlookup.
      * eapply IH.
        -- exact Hchild_actual.
        -- exact Hchild_local.
        -- exact Hchild_resolver.
        -- exact Hchild_context.
        -- exact Hchild_safe.
        -- exact Hchild_follow.
        -- exact Hchild_assembly.
        -- exact Hchild_continuation.
        -- exact Hchild_stop.
  - intros path items input rest trees Hderive IH.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hresolver Hcontext Hsafe Hfollow Hassembly
      Hcontinuation Hstop.
    destruct assembly_fuel as [| assembly_fuel].
    + discriminate Hassembly.
    + simpl in Hassembly.
      apply oracle_sequence.
      eapply IH.
      * exact Hactual.
      * exact Hlocal.
      * apply phase1_surface_sequence_initial_path_context.
        exact Hcontext.
      * exact Hsafe.
      * exact Hfollow.
      * exact Hassembly.
      * exact Hcontinuation.
  - intros path items index item input rest tree Hnth Hderive IH.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hresolver Hcontext Hsafe Hfollow Hassembly
      Hcontinuation Hstop.
    destruct follow_fuel as [| follow_fuel].
    + discriminate Hfollow.
    + destruct assembly_fuel as [| assembly_fuel].
      * discriminate Hassembly.
      * pose proof Hassembly as Hassembly_parent.
        simpl in Hassembly.
        apply andb_true_iff in Hassembly as [Hguard Halternatives].
        destruct
          (phase1_surface_choice_safe_alternative_member_fixed
            items index item Hsafe Hnth)
          as [Hnonnullable Hchild_safe].
        pose proof
          (follow_coverage_alternative_member
            follow_fuel outer_follow items index item Hfollow Hnth)
          as Hchild_follow.
        destruct
          (oracle_assembly_alternative_member_covered
            assembly_fuel canonical outer_follow 0 items index item
            Halternatives Hnth)
          as [child_assembly_fuel Hchild_assembly].
        replace (0 + index) with index in Hchild_assembly by lia.
        pose proof
          (phase1_surface_actual_canonical_path_descend
            path caller_prefix canonical (AtAlternative index) Hactual)
          as Hchild_actual.
        pose proof
          (phase1_surface_rule_local_path_descend
            canonical (AtAlternative index) Hlocal I)
          as Hchild_local.
        pose proof
          (phase1_surface_alternative_child_path_context
            path items index item Hcontext Hnth)
          as Hchild_context.
        pose proof
          (phase1_surface_alternative_descend_resolver_follow_compatible
            canonical outer_follow index)
          as Hchild_resolver.
        assert (Hchild_stop :
          phase1_surface_expression_stop_condition
            (descend path (AtAlternative index)) item rest).
        {
          destruct item as
            [literal | class_name | child_name | child_items | child_items |
             child_body | repetition_body]; simpl; try exact I.
          eapply phase1_surface_nontrailing_repetition_stop_fixed
            with (assembly_fuel := child_assembly_fuel)
                 (caller_prefix := caller_prefix)
                 (canonical := descend canonical (AtAlternative index))
                 (outer_follow := outer_follow).
          - exact Hchild_actual.
          - exact Hchild_local.
          - exact Hchild_context.
          - exact Hchild_safe.
          - exact Hchild_assembly.
          - apply phase1_surface_trailing_comma_nonsequence_descend_false.
            simpl. exact I.
          - exact Hcontinuation.
        }
        destruct Hresolver as [Hpattern Hproposition].
        assert (Hdecision :
          phase1_surface_predictive_oracle path input =
            Some (ChooseAlternative index)).
        {
          eapply phase1_surface_actual_canonical_oracle_alternative
            with (fuel := assembly_fuel) (caller_prefix := caller_prefix)
                 (canonical := canonical) (outer_follow := outer_follow)
                 (item := item) (rest := rest) (tree := tree).
          - exact Hactual.
          - apply phase1_surface_rule_local_path_nonempty.
            exact Hlocal.
          - exact Hcontext.
          - exact Hassembly_parent.
          - exact Hpattern.
          - exact Hproposition.
          - exact Hnth.
          - exact Hderive.
          - exact Hchild_safe.
          - exact Hnonnullable.
          - exact Hcontinuation.
        }
        apply oracle_alternative with item.
        -- exact Hdecision.
        -- exact Hnth.
        -- eapply IH.
           ++ exact Hchild_actual.
           ++ exact Hchild_local.
           ++ exact Hchild_resolver.
           ++ exact Hchild_context.
           ++ exact Hchild_safe.
           ++ exact Hchild_follow.
           ++ exact Hchild_assembly.
           ++ exact Hcontinuation.
           ++ exact Hchild_stop.
  - intros path body input.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hresolver Hcontext Hsafe Hfollow Hassembly
      Hcontinuation Hstop.
    destruct assembly_fuel as [| assembly_fuel].
    + discriminate Hassembly.
    + assert (Hdecision :
        phase1_surface_predictive_oracle path input =
          Some ChooseOptionalAbsent).
      {
        eapply phase1_surface_optional_absent_oracle
          with (choice_fuel := 255) (assembly_fuel := assembly_fuel)
               (canonical := canonical) (outer_follow := outer_follow).
        - exact Hcontext.
        - exact Hsafe.
        - unfold expression_fuel. lia.
        - exact Hassembly.
        - exact Hcontinuation.
      }
      apply oracle_optional_none.
      exact Hdecision.
  - intros path body input rest tree Hderive IH.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hresolver Hcontext Hsafe Hfollow Hassembly
      Hcontinuation Hstop.
    destruct follow_fuel as [| follow_fuel].
    + discriminate Hfollow.
    + destruct assembly_fuel as [| assembly_fuel].
      * discriminate Hassembly.
      * destruct
          (phase1_surface_choice_safe_optional_body_fixed body Hsafe)
          as [Hnonnullable Hchild_safe].
        pose proof
          (follow_coverage_optional_body
            follow_fuel outer_follow body Hfollow)
          as Hchild_follow.
        destruct
          (oracle_assembly_optional_covered
            assembly_fuel canonical outer_follow body Hassembly)
          as [Hdisjoint Hchild_assembly].
        pose proof
          (phase1_surface_actual_canonical_path_descend
            path caller_prefix canonical AtOptionalBody Hactual)
          as Hchild_actual.
        pose proof
          (phase1_surface_rule_local_path_descend
            canonical AtOptionalBody Hlocal I)
          as Hchild_local.
        pose proof
          (phase1_surface_optional_child_path_context
            path body Hcontext)
          as Hchild_context.
        pose proof
          (phase1_surface_optional_descend_resolver_follow_compatible
            canonical outer_follow)
          as Hchild_resolver.
        assert (Hchild_stop :
          phase1_surface_expression_stop_condition
            (descend path AtOptionalBody) body rest).
        {
          destruct body as
            [literal | class_name | child_name | child_items | child_items |
             child_body | repetition_body]; simpl; try exact I.
          eapply phase1_surface_nontrailing_repetition_stop_fixed
            with (assembly_fuel := assembly_fuel)
                 (caller_prefix := caller_prefix)
                 (canonical := descend canonical AtOptionalBody)
                 (outer_follow := outer_follow).
          - exact Hchild_actual.
          - exact Hchild_local.
          - exact Hchild_context.
          - exact Hchild_safe.
          - exact Hchild_assembly.
          - apply phase1_surface_trailing_comma_nonsequence_descend_false.
            simpl. exact I.
          - exact Hcontinuation.
        }
        assert (Hdecision :
          phase1_surface_predictive_oracle path input =
            Some ChooseOptionalPresent).
        {
          eapply phase1_surface_optional_present_oracle
            with (fuel := 255) (rest := rest) (tree := tree).
          - exact Hcontext.
          - exact Hsafe.
          - unfold expression_fuel. lia.
          - exact Hderive.
        }
        apply oracle_optional_some.
        -- exact Hdecision.
        -- eapply IH.
           ++ exact Hchild_actual.
           ++ exact Hchild_local.
           ++ exact Hchild_resolver.
           ++ exact Hchild_context.
           ++ exact Hchild_safe.
           ++ exact Hchild_follow.
           ++ exact Hchild_assembly.
           ++ exact Hcontinuation.
           ++ exact Hchild_stop.
  - intros path body input rest trees Hderive IH.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hresolver Hcontext Hsafe Hfollow Hassembly
      Hcontinuation Hstop.
    apply oracle_repetition.
    eapply IH.
    + exact Hactual.
    + exact Hlocal.
    + exact Hcontext.
    + exact Hsafe.
    + exact Hfollow.
    + exact Hassembly.
    + exact Hcontinuation.
    + exact Hstop.
  - intros path index input.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hcontext Hsafe Hfollow Hassembly Hcontinuation.
    constructor.
  - intros path index item items input middle rest tree trees
      Hitem IHitem Hitems IHitems.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hcontext Hsafe Hfollow Hassembly Hcontinuation.
    destruct follow_fuel as [| follow_fuel].
    + discriminate Hfollow.
    + destruct assembly_fuel as [| assembly_fuel].
      * discriminate Hassembly.
      * destruct
          (phase1_surface_choice_safe_sequence_cons_fixed
            item items Hsafe)
          as [Hitem_safe Htail_safe].
        pose proof
          (follow_coverage_sequence_head
            follow_fuel outer_follow item items Hfollow)
          as Hitem_follow.
        pose proof
          (follow_coverage_sequence_tail
            follow_fuel outer_follow item items Hfollow)
          as Htail_follow.
        destruct
          (oracle_assembly_sequence_cons_covered
            assembly_fuel canonical outer_follow index item items Hassembly)
          as [Hguard [Hitem_assembly Htail_assembly]].
        destruct
          (phase1_surface_sequence_child_actual_canonical_invariants
            path caller_prefix canonical index Hactual Hlocal)
          as [Hitem_actual Hitem_local].
        pose proof
          (phase1_surface_sequence_head_path_context
            path index item items Hcontext)
          as Hitem_context.
        pose proof
          (phase1_surface_sequence_tail_path_context
            path index item items Hcontext)
          as Htail_context.
        pose proof
          (phase1_surface_sequence_descend_resolver_follow_compatible
            canonical
            (phase1_surface_sequence_local_follow items outer_follow)
            index)
          as Hitem_resolver.
        pose proof
          (phase1_surface_sequence_choice_safe_for_continuation
            items Htail_safe)
          as Htail_forall_safe.
        assert (Hfuel_le : S 255 <= expression_fuel).
        { unfold expression_fuel. lia. }
        pose proof
          (phase1_surface_sequence_accepting_continuation_sound
            path (S index) items middle rest trees 255 outer_follow
            Hitems Hfuel_le Htail_forall_safe Hcontinuation)
          as Hmiddle_continuation.
        assert (Hitem_stop :
          phase1_surface_expression_stop_condition
            (descend path (AtSequence index)) item middle).
        {
          destruct item as
            [literal | class_name | child_name | child_items | child_items |
             child_body | repetition_body]; simpl; try exact I.
          destruct
            (trailing_comma_repeat_pathb
              (descend canonical (AtSequence index)))
            eqn:Htrail.
          - destruct
              (phase1_surface_sequence_head_trailing_assembly_context
                path caller_prefix canonical index repetition_body items
                outer_follow Hactual Hlocal Htrail Hguard)
              as [Hactual_trail [Hbody_shape Htail_shape]].
            eapply trailing_comma_sequence_tail_predictive_stops
              with (path := path) (index := index)
                   (items := items) (rest := rest) (trees := trees)
                   (outer_follow := outer_follow).
            + exact Hactual_trail.
            + exact Htail_shape.
            + exact Hitems.
            + exact Hcontinuation.
          - eapply phase1_surface_nontrailing_repetition_stop_fixed
              with (assembly_fuel := assembly_fuel)
                   (caller_prefix := caller_prefix)
                   (canonical := descend canonical (AtSequence index))
                   (outer_follow :=
                      phase1_surface_sequence_local_follow items outer_follow).
            + exact Hitem_actual.
            + exact Hitem_local.
            + exact Hitem_context.
            + exact Hitem_safe.
            + exact Hitem_assembly.
            + exact Htrail.
            + exact Hmiddle_continuation.
        }
        apply oracle_sequence_cons.
        -- eapply IHitem.
           ++ exact Hitem_actual.
           ++ exact Hitem_local.
           ++ exact Hitem_resolver.
           ++ exact Hitem_context.
           ++ exact Hitem_safe.
           ++ exact Hitem_follow.
           ++ exact Hitem_assembly.
           ++ exact Hmiddle_continuation.
           ++ exact Hitem_stop.
        -- eapply IHitems.
           ++ exact Hactual.
           ++ exact Hlocal.
           ++ exact Htail_context.
           ++ exact Htail_safe.
           ++ exact Htail_follow.
           ++ exact Htail_assembly.
           ++ exact Hcontinuation.
  - intros path body input.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hcontext Hsafe Hfollow Hassembly Hcontinuation Hstop.
    apply oracle_repetition_stop.
    exact Hstop.
  - intros path body input middle rest tree trees
      Hbody IHbody Hprogress Hrest IHrest.
    intros follow_fuel assembly_fuel caller_prefix canonical outer_follow
      Hactual Hlocal Hcontext Hsafe Hfollow Hassembly Hcontinuation Hstop.
    destruct follow_fuel as [| follow_fuel].
    + discriminate Hfollow.
    + destruct assembly_fuel as [| assembly_fuel].
      * discriminate Hassembly.
      * destruct
          (phase1_surface_choice_safe_repetition_body_fixed body Hsafe)
          as [Hnonnullable Hbody_safe].
        pose proof
          (follow_coverage_repetition_body
            follow_fuel outer_follow body Hfollow)
          as Hbody_follow.
        destruct
          (oracle_assembly_repetition_covered
            assembly_fuel canonical outer_follow body Hassembly)
          as [Hguard Hbody_assembly].
        pose proof
          (phase1_surface_actual_canonical_path_descend
            path caller_prefix canonical AtRepetitionBody Hactual)
          as Hbody_actual.
        pose proof
          (phase1_surface_rule_local_path_descend
            canonical AtRepetitionBody Hlocal I)
          as Hbody_local.
        pose proof
          (phase1_surface_repetition_child_path_context
            path body Hcontext)
          as Hbody_context.
        pose proof
          (phase1_surface_repetition_descend_resolver_follow_compatible
            canonical
            (phase1_surface_repetition_local_follow body outer_follow))
          as Hbody_resolver.
        pose proof
          (phase1_surface_repetition_accepting_continuation_sound
            path body middle rest trees expression_fuel outer_follow
            Hrest (le_n expression_fuel) Hbody_safe Hcontinuation)
          as Hmiddle_continuation.
        assert (Hbody_stop :
          phase1_surface_expression_stop_condition
            (descend path AtRepetitionBody) body middle).
        {
          destruct body as
            [literal | class_name | child_name | child_items | child_items |
             child_body | repetition_body]; simpl; try exact I.
          eapply phase1_surface_nontrailing_repetition_stop_fixed
            with (assembly_fuel := assembly_fuel)
                 (caller_prefix := caller_prefix)
                 (canonical := descend canonical AtRepetitionBody)
                 (outer_follow :=
                    phase1_surface_repetition_local_follow
                      (ERepetition repetition_body) outer_follow).
          - exact Hbody_actual.
          - exact Hbody_local.
          - exact Hbody_context.
          - exact Hbody_safe.
          - exact Hbody_assembly.
          - apply phase1_surface_trailing_comma_nonsequence_descend_false.
            simpl. exact I.
          - exact Hmiddle_continuation.
        }
        assert (Hdecision :
          phase1_surface_predictive_oracle path input =
            Some ChooseRepetitionContinue).
        {
          destruct (trailing_comma_repeat_pathb canonical) eqn:Htrail.
          - pose proof
              (phase1_surface_actual_canonical_trailing_comma_equation
                path caller_prefix canonical Hactual Hlocal)
              as Htrail_equation.
            rewrite Htrail in Htrail_equation.
            pose proof
              (repetition_assembly_guard_trailing
                canonical outer_follow body Htrail Hguard)
              as Hbody_shape.
            apply phase1_surface_predictive_oracle_trailing_path.
            + exact Htrail_equation.
            + eapply trailing_comma_body_derivation_continues.
              * exact Hbody_shape.
              * exact Hbody.
          - eapply phase1_surface_nontrailing_repetition_continue_oracle
              with (choice_fuel := 255) (caller_prefix := caller_prefix)
                   (canonical := canonical) (rest := middle) (tree := tree).
            + exact Hactual.
            + exact Hlocal.
            + exact Hcontext.
            + exact Hsafe.
            + unfold expression_fuel. lia.
            + exact Htrail.
            + exact Hbody.
        }
        apply oracle_repetition_step.
        -- exact Hdecision.
        -- eapply IHbody.
           ++ exact Hbody_actual.
           ++ exact Hbody_local.
           ++ exact Hbody_resolver.
           ++ exact Hbody_context.
           ++ exact Hbody_safe.
           ++ exact Hbody_follow.
           ++ exact Hbody_assembly.
           ++ exact Hmiddle_continuation.
           ++ exact Hbody_stop.
        -- exact Hprogress.
        -- eapply IHrest.
           ++ exact Hactual.
           ++ exact Hlocal.
           ++ exact Hcontext.
           ++ exact Hsafe.
           ++ exact Hfollow.
           ++ exact Hassembly.
           ++ exact Hcontinuation.
           ++ exact Hstop.
Qed.

Theorem phase1_surface_complete_derivation_predictive_oracle :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    OracleResolvedPhase1CompleteDerivation
      phase1_surface_predictive_oracle tokens tree.
Proof.
  intros tokens tree Hderive.
  unfold Phase1CompleteDerivation, CompleteDerivation in Hderive.
  inversion Hderive as
    [| | path name body input rest child_tree Hlookup Hbody | | | | |];
    subst.
  pose proof
    (phase1_surface_complete_nonterminal_reset_invariants
      255 [] phase1_surface_start_follow phase1_surface_start body []
      phase1_surface_root_expression_path_context
      Hlookup phase1_surface_root_follow_covered
      phase1_surface_start_follow_accepts_eof)
    as Hreset.
  destruct Hreset as
    [Hchild_actual
      [Hchild_local
        [Hchild_resolver
          [Hchild_context
            [Hchild_safe
              [Hchild_follow
                [Hchild_assembly
                  [Hchild_continuation Hresolver_equation]]]]]]]].
  assert (Hchild_stop :
    phase1_surface_expression_stop_condition
      (descend [] (AtNonterminal phase1_surface_start)) body []).
  {
    destruct body as
      [literal | class_name | child_name | items | items |
       child_body | repetition_body]; simpl; try exact I.
    eapply phase1_surface_nontrailing_repetition_stop_fixed
      with (assembly_fuel := oracle_assembly_fuel)
           (caller_prefix := [])
           (canonical := [AtNonterminal phase1_surface_start])
           (outer_follow := phase1_surface_start_follow).
    - exact Hchild_actual.
    - exact Hchild_local.
    - exact Hchild_context.
    - exact Hchild_safe.
    - exact Hchild_assembly.
    - apply phase1_surface_trailing_comma_nonsequence_descend_false
        with (path := []).
      simpl. exact I.
    - exact Hchild_continuation.
  }
  unfold OracleResolvedPhase1CompleteDerivation,
    OracleResolvedExpression.
  apply oracle_nonterminal with body.
  - exact Hlookup.
  - eapply (proj1 phase1_surface_rule_local_derivation_predictive).
    + exact Hbody.
    + exact Hchild_actual.
    + exact Hchild_local.
    + exact Hchild_resolver.
    + exact Hchild_context.
    + exact Hchild_safe.
    + exact Hchild_follow.
    + exact Hchild_assembly.
    + exact Hchild_continuation.
    + exact Hchild_stop.
Qed.
