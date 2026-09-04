From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationLookahead
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyContinuationSoundness.

Import ListNotations.

(*
  Predictive-fallback foundation for the final PHIL-SURFACE-DETERM-001 bridge.

  #712 established exact path contexts for ordinary derivations.  This file
  handles the other implementation-independent half of the final mutual
  induction: when a choice point is not claimed by a certified overlap
  resolver, ordinary derivation evidence agrees with the nullable/FIRST-based
  fallback decision.

  The lemmas stay deliberately local.  The successor bridge only has to supply
  the already-computed no-overlap/continuation facts at the current exact path;
  it does not have to reopen FIRST witnesses or the fallback search mechanics.
*)

Lemma phase1_surface_nonnullable_derivation_makes_progress :
  forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    choice_bodies_nonnullable_fuel
      expression_fuel expression = true ->
    nullable_expression
      phase1_surface_nullable_facts expression = false ->
    input <> rest.
Proof.
  intros path expression input rest tree
    Hderive Hsafe Hnonnullable Hequal.
  subst rest.
  pose proof
    (derives_no_consume_nullable_witness
      phase1_surface_rules path expression input tree Hderive)
    as Hnullable_witness.
  pose proof
    (phase1_surface_nullable_witness_matches_computed_facts
      expression Hnullable_witness Hsafe)
    as Hnullable.
  rewrite Hnonnullable in Hnullable.
  discriminate.
Qed.

Lemma phase1_surface_consuming_derivation_starts_inputb :
  forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    input <> rest ->
    choice_bodies_nonnullable_fuel
      expression_fuel expression = true ->
    expression_starts_inputb expression input = true.
Proof.
  intros path expression input rest tree Hderive Hprogress Hsafe.
  destruct input as [| first_token tail].
  - exfalso.
    apply Hprogress.
    destruct
      (derives_consumes_prefix
        phase1_surface_rules path expression [] rest tree Hderive)
      as [consumed Hprefix].
    destruct consumed as [| head consumed].
    + simpl in Hprefix.
      exact Hprefix.
    + discriminate Hprefix.
  - rewrite expression_starts_inputb_cons_equation.
    rewrite continuation_concrete_token_shapes_agree.
    eapply phase1_surface_first_witness_matches_computed_facts.
    + eapply derives_consuming_first_witness; eauto.
    + exact Hsafe.
Qed.

Corollary phase1_surface_nonnullable_derivation_starts_inputb :
  forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    choice_bodies_nonnullable_fuel
      expression_fuel expression = true ->
    nullable_expression
      phase1_surface_nullable_facts expression = false ->
    expression_starts_inputb expression input = true.
Proof.
  intros path expression input rest tree Hderive Hsafe Hnonnullable.
  eapply phase1_surface_consuming_derivation_starts_inputb.
  - exact Hderive.
  - eapply phase1_surface_nonnullable_derivation_makes_progress; eauto.
  - exact Hsafe.
Qed.

Lemma first_matching_alternative_selects_offset :
  forall relative items item input offset,
    nth_error items relative = Some item ->
    (forall earlier_index earlier_item,
      earlier_index < relative ->
      nth_error items earlier_index = Some earlier_item ->
      expression_starts_inputb earlier_item input = false) ->
    expression_starts_inputb item input = true ->
    first_matching_alternative offset items input =
      Some (offset + relative).
Proof.
  induction relative as [| relative IH];
    intros items item input offset Hnth Hearlier Hstart;
    destruct items as [| head rest]; simpl in Hnth; try discriminate.
  - inversion Hnth; subst head.
    simpl.
    rewrite Hstart, Nat.add_0_r.
    reflexivity.
  - assert (Hhead : expression_starts_inputb head input = false).
    {
      eapply Hearlier with (earlier_index := 0) (earlier_item := head).
      - lia.
      - reflexivity.
    }
    assert (Hrest_earlier :
      forall earlier_index earlier_item,
        earlier_index < relative ->
        nth_error rest earlier_index = Some earlier_item ->
        expression_starts_inputb earlier_item input = false).
    {
      intros earlier_index earlier_item Hlt Hlookup.
      eapply Hearlier with
        (earlier_index := S earlier_index)
        (earlier_item := earlier_item).
      - lia.
      - simpl. exact Hlookup.
    }
    simpl.
    rewrite Hhead.
    pose proof
      (IH rest item input (S offset)
        Hnth Hrest_earlier Hstart) as Hselected.
    replace (offset + S relative) with (S offset + relative) by lia.
    exact Hselected.
Qed.

Corollary first_matching_alternative_selects_index :
  forall items index item input,
    nth_error items index = Some item ->
    (forall earlier_index earlier_item,
      earlier_index < index ->
      nth_error items earlier_index = Some earlier_item ->
      expression_starts_inputb earlier_item input = false) ->
    expression_starts_inputb item input = true ->
    first_matching_alternative 0 items input = Some index.
Proof.
  intros items index item input Hnth Hearlier Hstart.
  change (first_matching_alternative 0 items input = Some (0 + index)).
  eapply first_matching_alternative_selects_offset; eauto.
Qed.

Theorem predictive_fallback_alternative_from_derivation :
  forall path items index item input rest tree,
    nth_error items index = Some item ->
    Derives phase1_surface_rules
      (descend path (AtAlternative index))
      item input rest tree ->
    choice_bodies_nonnullable_fuel
      expression_fuel item = true ->
    nullable_expression
      phase1_surface_nullable_facts item = false ->
    (forall earlier_index earlier_item,
      earlier_index < index ->
      nth_error items earlier_index = Some earlier_item ->
      expression_starts_inputb earlier_item input = false) ->
    predictive_fallback_decision (EAlternative items) input =
      Some (ChooseAlternative index).
Proof.
  intros path items index item input rest tree
    Hnth Hderive Hsafe Hnonnullable Hearlier.
  unfold predictive_fallback_decision.
  rewrite
    (first_matching_alternative_selects_index
      items index item input Hnth Hearlier
      (phase1_surface_nonnullable_derivation_starts_inputb
        (descend path (AtAlternative index))
        item input rest tree Hderive Hsafe Hnonnullable)).
  reflexivity.
Qed.

Theorem predictive_fallback_optional_present_from_derivation :
  forall path body input rest tree,
    Derives phase1_surface_rules
      (descend path AtOptionalBody) body input rest tree ->
    choice_bodies_nonnullable_fuel
      expression_fuel body = true ->
    nullable_expression
      phase1_surface_nullable_facts body = false ->
    predictive_fallback_decision (EOptional body) input =
      Some ChooseOptionalPresent.
Proof.
  intros path body input rest tree Hderive Hsafe Hnonnullable.
  unfold predictive_fallback_decision.
  rewrite
    (phase1_surface_nonnullable_derivation_starts_inputb
      (descend path AtOptionalBody)
      body input rest tree Hderive Hsafe Hnonnullable).
  reflexivity.
Qed.

Theorem predictive_fallback_repetition_continue_from_derivation :
  forall path body input rest tree,
    Derives phase1_surface_rules
      (descend path AtRepetitionBody) body input rest tree ->
    choice_bodies_nonnullable_fuel
      expression_fuel body = true ->
    nullable_expression
      phase1_surface_nullable_facts body = false ->
    predictive_fallback_decision (ERepetition body) input =
      Some ChooseRepetitionContinue.
Proof.
  intros path body input rest tree Hderive Hsafe Hnonnullable.
  unfold predictive_fallback_decision.
  rewrite
    (phase1_surface_nonnullable_derivation_starts_inputb
      (descend path AtRepetitionBody)
      body input rest tree Hderive Hsafe Hnonnullable).
  reflexivity.
Qed.

Theorem predictive_fallback_optional_absent_from_continuation :
  forall body input outer_follow,
    nullable_expression
      phase1_surface_nullable_facts body = false ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body)
      outer_follow = [] ->
    continuation_lookahead_mem input outer_follow = true ->
    predictive_fallback_decision (EOptional body) input =
      Some ChooseOptionalAbsent.
Proof.
  intros body input outer_follow Hnullable Hdisjoint Hcontinuation.
  unfold predictive_fallback_decision.
  rewrite
    (accepting_continuation_excludes_body_start_without_overlap
      body input outer_follow Hnullable Hdisjoint Hcontinuation).
  reflexivity.
Qed.

Theorem predictive_fallback_repetition_stop_from_continuation :
  forall body input outer_follow,
    nullable_expression
      phase1_surface_nullable_facts body = false ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body)
      outer_follow = [] ->
    continuation_lookahead_mem input outer_follow = true ->
    predictive_fallback_decision (ERepetition body) input =
      Some ChooseRepetitionStop.
Proof.
  intros body input outer_follow Hnullable Hdisjoint Hcontinuation.
  unfold predictive_fallback_decision.
  rewrite
    (accepting_continuation_excludes_body_start_without_overlap
      body input outer_follow Hnullable Hdisjoint Hcontinuation).
  reflexivity.
Qed.
