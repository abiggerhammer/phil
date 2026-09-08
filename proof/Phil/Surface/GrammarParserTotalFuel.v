From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyMutualPredictiveBridge
  GrammarDeterminacyPredictiveOracle
  GrammarParserGoalRank
  GrammarParserGlobalGoalRank
  GrammarParserRecognizer
  GrammarParserProgress
  GrammarParserTotalFuelStatic
  GrammarParserZeroConsumeNullable.

Import ListNotations.
Open Scope string_scope.

Opaque phase1_surface_rules
  phase1_surface_nullable_facts
  phase1_surface_parser_rank_facts
  phase1_surface_parser_global_goal_rank_bound
  phase1_surface_predictive_oracle.

(*
  Concrete finite-fuel completeness for PHIL-SURFACE-GRAMMAR-CORR-001.

  Runtime parser recursion is measured lexicographically:

    1. remaining ConcreteToken count; then
    2. the exact Grammar-v1 zero-consumption goal rank.

  GrammarParserTotalFuelStatic.v keeps every recursive goal inside the exact
  global rank universe certified by #826.  #819 proves strict token decrease on
  progress, #824 identifies zero-consuming sequence heads as nullable, and #820
  proves strict rank decrease on every same-input parser edge.

  The reference recognizer consumes one unit of fuel per recursive call depth,
  not per unit of total work.  Therefore sequence/repetition two-child cases use
  max(child fuel), not the conservative sum used by the earlier eventual-
  completeness theorem.
*)

Definition phase1_surface_parser_local_measure
  (input : list ConcreteToken)
  (rank : nat) : nat :=
  S
    (List.length input * phase1_surface_parser_global_goal_rank_bound +
     rank).

Lemma phase1_surface_same_input_measure_fits_parent_remaining :
  forall input child_rank parent_rank,
    child_rank < parent_rank ->
    phase1_surface_parser_local_measure input child_rank <=
      List.length input * phase1_surface_parser_global_goal_rank_bound +
      parent_rank.
Proof.
  intros input child_rank parent_rank Hrank.
  unfold phase1_surface_parser_local_measure.
  lia.
Qed.

Lemma phase1_surface_progress_measure_fits_parent_remaining :
  forall (input middle : list ConcreteToken) child_rank parent_rank,
    List.length middle < List.length input ->
    child_rank < phase1_surface_parser_global_goal_rank_bound ->
    phase1_surface_parser_local_measure middle child_rank <=
      List.length input * phase1_surface_parser_global_goal_rank_bound +
      parent_rank.
Proof.
  intros input middle child_rank parent_rank Hlength Hrank.
  pose proof phase1_surface_parser_global_goal_rank_bound_positive as Hpositive.
  unfold phase1_surface_parser_local_measure.
  nia.
Qed.

Lemma oracle_parse_fuel_nonterminal_step :
  forall fuel oracle rules path name input,
    oracle_parse_fuel
      (S fuel) oracle rules
      (GoalExpression path (ENonterminal name)) input =
    match lookupRule name rules with
    | Some body =>
        match
          oracle_parse_fuel fuel oracle rules
            (GoalExpression
              (descend path (AtNonterminal name)) body)
            input
        with
        | Some (rest, ResultTree tree) =>
            Some (rest, ResultTree (PTNonterminal name tree))
        | _ => None
        end
    | None => None
    end.
Proof.
  reflexivity.
Qed.

Lemma oracle_parse_fuel_nonterminal_complete_lift :
  forall child_required oracle rules path name body input rest tree,
    lookupRule name rules = Some body ->
    (forall extra,
      oracle_parse_fuel
        (child_required + extra) oracle rules
        (GoalExpression (descend path (AtNonterminal name)) body)
        input = Some (rest, ResultTree tree)) ->
    forall extra,
      oracle_parse_fuel
        (S child_required + extra) oracle rules
        (GoalExpression path (ENonterminal name)) input =
      Some (rest, ResultTree (PTNonterminal name tree)).
Proof.
  intros child_required oracle rules path name body input rest tree
    Hlookup Hchild_complete extra.
  replace (S child_required + extra)
    with (S (child_required + extra)) by lia.
  rewrite oracle_parse_fuel_nonterminal_step.
  rewrite Hlookup.
  rewrite (Hchild_complete extra).
  reflexivity.
Qed.

Definition phase1_surface_parser_bounded_complete
  (goal : DerivationGoal)
  (input rest : list ConcreteToken)
  (result : DerivationResult) : Prop :=
  forall static_fuel rank,
    phase1_surface_parser_goal_rank_fuel static_fuel goal = Some rank ->
    phase1_surface_parser_goal_options_global static_fuel goal ->
    phase1_surface_parser_goal_choice_safe static_fuel goal ->
    static_fuel <= expression_fuel ->
    exists required,
      required <= phase1_surface_parser_local_measure input rank /\
      forall extra,
        oracle_parse_fuel
          (required + extra)
          phase1_surface_predictive_oracle
          phase1_surface_rules
          goal input = Some (rest, result).

Lemma phase1_surface_sequence_cons_bounded_complete :
  forall path index item items input middle rest tree trees,
    OracleDerives
      phase1_surface_predictive_oracle phase1_surface_rules
      (GoalExpression (descend path (AtSequence index)) item)
      input middle (ResultTree tree) ->
    phase1_surface_parser_bounded_complete
      (GoalExpression (descend path (AtSequence index)) item)
      input middle (ResultTree tree) ->
    OracleDerives
      phase1_surface_predictive_oracle phase1_surface_rules
      (GoalSequence path (S index) items)
      middle rest (ResultTrees trees) ->
    phase1_surface_parser_bounded_complete
      (GoalSequence path (S index) items)
      middle rest (ResultTrees trees) ->
    phase1_surface_parser_bounded_complete
      (GoalSequence path index (item :: items))
      input rest (ResultTrees (tree :: trees)).
Proof.
  intros path index item items input middle rest tree trees
    Hhead IHhead Htail IHtail.
  unfold phase1_surface_parser_bounded_complete in IHhead, IHtail |- *.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  assert (Hhead_global :
    phase1_surface_parser_goal_options_global
      static_fuel
      (GoalExpression (descend path (AtSequence index)) item)).
  {
    eapply phase1_surface_sequence_head_options_global.
    exact Hglobal.
  }
  assert (Htail_global :
    phase1_surface_parser_goal_options_global
      static_fuel (GoalSequence path (S index) items)).
  {
    eapply phase1_surface_sequence_tail_options_global.
    exact Hglobal.
  }
  destruct
    (phase1_surface_sequence_cons_choice_safe
      static_fuel path index item items Hsafe)
    as [Hhead_safe Htail_safe].
  destruct
    (phase1_surface_parser_goal_rank_exists
      static_fuel
      (GoalExpression (descend path (AtSequence index)) item)
      Hhead_global)
    as [head_rank Hhead_rank].
  destruct
    (phase1_surface_parser_goal_rank_exists
      static_fuel (GoalSequence path (S index) items)
      Htail_global)
    as [tail_rank Htail_rank].
  pose proof Hrank as Hparent_rank_raw.
  pose proof Hhead_rank as Hhead_rank_raw.
  pose proof Htail_rank as Htail_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in
    Hparent_rank_raw, Hhead_rank_raw, Htail_rank_raw.
  assert (Hhead_decrease : head_rank < rank).
  {
    eapply parser_sequence_head_rank_decreases; eauto.
  }
  destruct
    (IHhead
      static_fuel head_rank
      Hhead_rank Hhead_global Hhead_safe Hsfuel)
    as [head_required [Hhead_required Hhead_complete]].
  destruct
    (IHtail
      static_fuel tail_rank
      Htail_rank Htail_global Htail_safe Hsfuel)
    as [tail_required [Htail_required Htail_complete]].
  assert (Hhead_fit :
    head_required <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    eapply Nat.le_trans.
    - exact Hhead_required.
    - eapply phase1_surface_same_input_measure_fits_parent_remaining.
      exact Hhead_decrease.
  }
  assert (Htail_fit :
    tail_required <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    destruct (list_eq_dec concrete_token_eq_dec input middle)
      as [Hequal | Hprogress].
    - subst middle.
      assert (Hhead_safe_static :
        choice_bodies_nonnullable_fuel static_fuel item = true).
      {
        eapply phase1_surface_expression_goal_choice_safe_bool.
        exact Hhead_safe.
      }
      assert (Hhead_safe_full :
        choice_bodies_nonnullable_fuel expression_fuel item = true).
      {
        eapply choice_bodies_nonnullable_fuel_monotone.
        + exact Hsfuel.
        + exact Hhead_safe_static.
      }
      pose proof
        (phase1_surface_zero_consume_oracle_expression_is_nullable
          phase1_surface_predictive_oracle
          (descend path (AtSequence index))
          item input tree Hhead Hhead_safe_full)
        as Hnullable.
      assert (Htail_decrease : tail_rank < rank).
      {
        eapply parser_sequence_nullable_tail_rank_decreases; eauto.
      }
      eapply Nat.le_trans.
      + exact Htail_required.
      + eapply phase1_surface_same_input_measure_fits_parent_remaining.
        exact Htail_decrease.
    - pose proof
        (oracle_derivation_progress_decreases_length
          phase1_surface_predictive_oracle phase1_surface_rules
          (GoalExpression (descend path (AtSequence index)) item)
          input middle (ResultTree tree) Hhead Hprogress)
        as Hlength.
      pose proof
        (phase1_surface_parser_goal_rank_below_global_bound
          static_fuel (GoalSequence path (S index) items)
          tail_rank Htail_global Htail_rank)
        as Htail_bound.
      eapply Nat.le_trans.
      + exact Htail_required.
      + eapply phase1_surface_progress_measure_fits_parent_remaining; eauto.
  }
  assert (Hmax_fit :
    Nat.max head_required tail_required <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    apply Nat.max_lub; assumption.
  }
  exists (S (Nat.max head_required tail_required)).
  split.
  - unfold phase1_surface_parser_local_measure.
    lia.
  - intros extra.
    simpl.
    replace
      (Nat.max head_required tail_required + extra)
      with
      (head_required +
        ((Nat.max head_required tail_required - head_required) + extra))
      by lia.
    rewrite
      (Hhead_complete
        ((Nat.max head_required tail_required - head_required) + extra)).
    replace
      (head_required +
        ((Nat.max head_required tail_required - head_required) + extra))
      with
      (tail_required +
        ((Nat.max head_required tail_required - tail_required) + extra))
      by lia.
    rewrite
      (Htail_complete
        ((Nat.max head_required tail_required - tail_required) + extra)).
    reflexivity.
Qed.

Lemma phase1_surface_repetition_step_bounded_complete :
  forall path body input middle rest tree trees,
    phase1_surface_predictive_oracle path input =
      Some ChooseRepetitionContinue ->
    OracleDerives
      phase1_surface_predictive_oracle phase1_surface_rules
      (GoalExpression (descend path AtRepetitionBody) body)
      input middle (ResultTree tree) ->
    phase1_surface_parser_bounded_complete
      (GoalExpression (descend path AtRepetitionBody) body)
      input middle (ResultTree tree) ->
    input <> middle ->
    OracleDerives
      phase1_surface_predictive_oracle phase1_surface_rules
      (GoalRepetition path body)
      middle rest (ResultTrees trees) ->
    phase1_surface_parser_bounded_complete
      (GoalRepetition path body)
      middle rest (ResultTrees trees) ->
    phase1_surface_parser_bounded_complete
      (GoalRepetition path body)
      input rest (ResultTrees (tree :: trees)).
Proof.
  intros path body input middle rest tree trees
    Hdecision Hbody IHbody Hprogress Htail IHtail.
  unfold phase1_surface_parser_bounded_complete in IHbody, IHtail |- *.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  assert (Hbody_global :
    phase1_surface_parser_goal_options_global
      static_fuel
      (GoalExpression (descend path AtRepetitionBody) body)).
  {
    eapply phase1_surface_repetition_body_options_global.
    exact Hglobal.
  }
  assert (Hbody_safe :
    phase1_surface_parser_goal_choice_safe
      static_fuel
      (GoalExpression (descend path AtRepetitionBody) body)).
  {
    eapply phase1_surface_repetition_body_choice_safe.
    exact Hsafe.
  }
  destruct
    (phase1_surface_parser_goal_rank_exists
      static_fuel
      (GoalExpression (descend path AtRepetitionBody) body)
      Hbody_global)
    as [body_rank Hbody_rank].
  pose proof Hrank as Hparent_rank_raw.
  pose proof Hbody_rank as Hbody_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in
    Hparent_rank_raw, Hbody_rank_raw.
  assert (Hbody_decrease : body_rank < rank).
  {
    eapply parser_repetition_body_rank_decreases; eauto.
  }
  destruct
    (IHbody
      static_fuel body_rank
      Hbody_rank Hbody_global Hbody_safe Hsfuel)
    as [body_required [Hbody_required Hbody_complete]].
  destruct
    (IHtail
      static_fuel rank
      Hrank Hglobal Hsafe Hsfuel)
    as [tail_required [Htail_required Htail_complete]].
  assert (Hbody_fit :
    body_required <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    eapply Nat.le_trans.
    - exact Hbody_required.
    - eapply phase1_surface_same_input_measure_fits_parent_remaining.
      exact Hbody_decrease.
  }
  assert (Hparent_bound :
    rank < phase1_surface_parser_global_goal_rank_bound).
  {
    exact
      (phase1_surface_parser_goal_rank_below_global_bound
        static_fuel (GoalRepetition path body)
        rank Hglobal Hrank).
  }
  pose proof
    (oracle_derivation_progress_decreases_length
      phase1_surface_predictive_oracle phase1_surface_rules
      (GoalExpression (descend path AtRepetitionBody) body)
      input middle (ResultTree tree) Hbody Hprogress)
    as Hlength.
  assert (Htail_fit :
    tail_required <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    eapply Nat.le_trans.
    - exact Htail_required.
    - eapply phase1_surface_progress_measure_fits_parent_remaining; eauto.
  }
  assert (Hmax_fit :
    Nat.max body_required tail_required <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    apply Nat.max_lub; assumption.
  }
  exists (S (Nat.max body_required tail_required)).
  split.
  - unfold phase1_surface_parser_local_measure.
    lia.
  - intros extra.
    simpl.
    rewrite Hdecision.
    replace
      (Nat.max body_required tail_required + extra)
      with
      (body_required +
        ((Nat.max body_required tail_required - body_required) + extra))
      by lia.
    rewrite
      (Hbody_complete
        ((Nat.max body_required tail_required - body_required) + extra)).
    destruct (list_eq_dec concrete_token_eq_dec input middle)
      as [Hequal | Hdifferent].
    {
      exfalso.
      apply Hprogress.
      exact Hequal.
    }
    {
      replace
        (body_required +
          ((Nat.max body_required tail_required - body_required) + extra))
        with
        (tail_required +
          ((Nat.max body_required tail_required - tail_required) + extra))
        by lia.
      rewrite
        (Htail_complete
          ((Nat.max body_required tail_required - tail_required) + extra)).
      reflexivity.
    }
Qed.

Lemma phase1_surface_literal_bounded_complete :
  forall path literal tail,
    phase1_surface_parser_bounded_complete
      (GoalExpression path (ELiteral literal))
      (TLiteral literal :: tail) tail
      (ResultTree (PTLiteral literal)).
Proof.
  intros path literal tail.
  unfold phase1_surface_parser_bounded_complete.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  exists 1.
  split.
  - unfold phase1_surface_parser_local_measure. lia.
  - intros extra.
    simpl.
    rewrite String.eqb_refl.
    reflexivity.
Qed.

Lemma phase1_surface_lexical_bounded_complete :
  forall path class lexeme tail,
    phase1_surface_parser_bounded_complete
      (GoalExpression path (ELexicalClass class))
      (TLexical class lexeme :: tail) tail
      (ResultTree (PTLexical class lexeme)).
Proof.
  intros path class lexeme tail.
  unfold phase1_surface_parser_bounded_complete.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  exists 1.
  split.
  - unfold phase1_surface_parser_local_measure. lia.
  - intros extra.
    simpl.
    rewrite String.eqb_refl.
    reflexivity.
Qed.

Lemma phase1_surface_nonterminal_bounded_complete :
  forall path name body input rest tree,
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_parser_bounded_complete
      (GoalExpression (descend path (AtNonterminal name)) body)
      input rest (ResultTree tree) ->
    phase1_surface_parser_bounded_complete
      (GoalExpression path (ENonterminal name))
      input rest (ResultTree (PTNonterminal name tree)).
Proof.
  intros path name body input rest tree Hlookup IHbody.
  unfold phase1_surface_parser_bounded_complete in IHbody |- *.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  unfold phase1_surface_parser_goal_rank_fuel in Hrank.
  destruct static_fuel as [| static_fuel]; try discriminate Hrank.
  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)).
  {
    abstract (
      eapply phase1_surface_lookup_rule_goal_options_global;
      exact Hlookup).
  }
  assert (Hchild_safe :
    phase1_surface_parser_goal_choice_safe
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)).
  {
    abstract (
      constructor;
      unfold phase1_surface_parser_goal_choice_safe_structural;
      apply phase1_surface_expression_choice_safe_of_bool;
      eapply phase1_surface_lookup_rule_choice_safe;
      exact Hlookup).
  }
  destruct
    (phase1_surface_parser_goal_rank_exists
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)
      Hchild_global)
    as [child_rank Hchild_rank].
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < rank).
  {
    abstract (
      eapply phase1_surface_nonterminal_child_rank_decreases_fuel; eauto).
  }
  destruct
    (IHbody
      expression_fuel child_rank
      Hchild_rank Hchild_global Hchild_safe (Nat.le_refl _))
    as [child_required [Hchild_required Hchild_complete]].
  assert (Hchild_fit :
    phase1_surface_parser_local_measure input child_rank <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    abstract (
      eapply phase1_surface_same_input_measure_fits_parent_remaining;
      exact Hdecrease).
  }
  exists (S child_required).
  split.
  - abstract (
      unfold phase1_surface_parser_local_measure in *;
      lia).
  - intros extra.
    exact
      (oracle_parse_fuel_nonterminal_complete_lift
        child_required
        phase1_surface_predictive_oracle phase1_surface_rules
        path name body input rest tree
        Hlookup Hchild_complete extra).
Qed.

Lemma phase1_surface_sequence_wrapper_bounded_complete :
  forall path items input rest trees,
    phase1_surface_parser_bounded_complete
      (GoalSequence path 0 items)
      input rest (ResultTrees trees) ->
    phase1_surface_parser_bounded_complete
      (GoalExpression path (ESequence items))
      input rest (ResultTree (PTSequence trees)).
Proof.
  intros path items input rest trees IHitems.
  unfold phase1_surface_parser_bounded_complete in IHitems |- *.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  unfold phase1_surface_parser_goal_rank_fuel in Hrank.
  destruct static_fuel as [| static_fuel]; try discriminate Hrank.
  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      static_fuel (GoalSequence path 0 items)).
  {
    eapply phase1_surface_sequence_wrapper_options_global.
    exact Hglobal.
  }
  assert (Hchild_safe :
    phase1_surface_parser_goal_choice_safe
      static_fuel (GoalSequence path 0 items)).
  {
    eapply phase1_surface_sequence_wrapper_choice_safe.
    exact Hsafe.
  }
  destruct
    (phase1_surface_parser_goal_rank_exists
      static_fuel (GoalSequence path 0 items) Hchild_global)
    as [child_rank Hchild_rank].
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < rank).
  {
    eapply parser_sequence_wrapper_rank_decreases; eauto.
  }
  assert (Hchild_fuel : static_fuel <= expression_fuel) by lia.
  destruct
    (IHitems
      static_fuel child_rank
      Hchild_rank Hchild_global Hchild_safe Hchild_fuel)
    as [child_required [Hchild_required Hchild_complete]].
  assert (Hchild_fit :
    phase1_surface_parser_local_measure input child_rank <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    eapply phase1_surface_same_input_measure_fits_parent_remaining.
    exact Hdecrease.
  }
  exists (S child_required).
  split.
  - unfold phase1_surface_parser_local_measure in *.
    lia.
  - intros extra.
    simpl.
    rewrite (Hchild_complete extra).
    reflexivity.
Qed.

Lemma phase1_surface_alternative_bounded_complete :
  forall path items index item input rest tree,
    phase1_surface_predictive_oracle path input =
      Some (ChooseAlternative index) ->
    nth_error items index = Some item ->
    phase1_surface_parser_bounded_complete
      (GoalExpression (descend path (AtAlternative index)) item)
      input rest (ResultTree tree) ->
    phase1_surface_parser_bounded_complete
      (GoalExpression path (EAlternative items))
      input rest (ResultTree (PTAlternative index tree)).
Proof.
  intros path items index item input rest tree Hdecision Hnth IHitem.
  unfold phase1_surface_parser_bounded_complete in IHitem |- *.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  unfold phase1_surface_parser_goal_rank_fuel in Hrank.
  destruct static_fuel as [| static_fuel]; try discriminate Hrank.
  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      static_fuel
      (GoalExpression (descend path (AtAlternative index)) item)).
  {
    eapply phase1_surface_alternative_member_options_global; eauto.
  }
  assert (Hchild_safe :
    phase1_surface_parser_goal_choice_safe
      static_fuel
      (GoalExpression (descend path (AtAlternative index)) item)).
  {
    eapply phase1_surface_alternative_member_choice_safe; eauto.
  }
  destruct
    (phase1_surface_parser_goal_rank_exists
      static_fuel
      (GoalExpression (descend path (AtAlternative index)) item)
      Hchild_global)
    as [child_rank Hchild_rank].
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  destruct
    (parser_alternative_goal_rank_fuel
      static_fuel phase1_surface_parser_rank_facts items)
    as [alternative_rank |] eqn:Halternative.
  2: {
    rewrite parser_expression_alternative_rank_equation in Hrank.
    rewrite Halternative in Hrank.
    discriminate Hrank.
  }
  assert (Hdecrease : child_rank < rank).
  {
    eapply parser_alternative_member_rank_decreases; eauto.
  }
  assert (Hchild_fuel : static_fuel <= expression_fuel) by lia.
  destruct
    (IHitem
      static_fuel child_rank
      Hchild_rank Hchild_global Hchild_safe Hchild_fuel)
    as [child_required [Hchild_required Hchild_complete]].
  assert (Hchild_fit :
    phase1_surface_parser_local_measure input child_rank <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    eapply phase1_surface_same_input_measure_fits_parent_remaining.
    exact Hdecrease.
  }
  exists (S child_required).
  split.
  - unfold phase1_surface_parser_local_measure in *.
    lia.
  - intros extra.
    simpl.
    rewrite Hdecision.
    rewrite Hnth.
    rewrite (Hchild_complete extra).
    reflexivity.
Qed.

Lemma phase1_surface_optional_none_bounded_complete :
  forall path body input,
    phase1_surface_predictive_oracle path input = Some ChooseOptionalAbsent ->
    phase1_surface_parser_bounded_complete
      (GoalExpression path (EOptional body))
      input input (ResultTree PTOptionalNone).
Proof.
  intros path body input Hdecision.
  unfold phase1_surface_parser_bounded_complete.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  exists 1.
  split.
  - unfold phase1_surface_parser_local_measure. lia.
  - intros extra.
    simpl.
    rewrite Hdecision.
    reflexivity.
Qed.

Lemma phase1_surface_optional_some_bounded_complete :
  forall path body input rest tree,
    phase1_surface_predictive_oracle path input = Some ChooseOptionalPresent ->
    phase1_surface_parser_bounded_complete
      (GoalExpression (descend path AtOptionalBody) body)
      input rest (ResultTree tree) ->
    phase1_surface_parser_bounded_complete
      (GoalExpression path (EOptional body))
      input rest (ResultTree (PTOptionalSome tree)).
Proof.
  intros path body input rest tree Hdecision IHbody.
  unfold phase1_surface_parser_bounded_complete in IHbody |- *.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  unfold phase1_surface_parser_goal_rank_fuel in Hrank.
  destruct static_fuel as [| static_fuel]; try discriminate Hrank.
  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      static_fuel
      (GoalExpression (descend path AtOptionalBody) body)).
  {
    eapply phase1_surface_optional_body_options_global.
    exact Hglobal.
  }
  assert (Hchild_safe :
    phase1_surface_parser_goal_choice_safe
      static_fuel
      (GoalExpression (descend path AtOptionalBody) body)).
  {
    eapply phase1_surface_optional_body_choice_safe.
    exact Hsafe.
  }
  destruct
    (phase1_surface_parser_goal_rank_exists
      static_fuel
      (GoalExpression (descend path AtOptionalBody) body)
      Hchild_global)
    as [child_rank Hchild_rank].
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < rank).
  {
    eapply parser_optional_body_rank_decreases; eauto.
  }
  assert (Hchild_fuel : static_fuel <= expression_fuel) by lia.
  destruct
    (IHbody
      static_fuel child_rank
      Hchild_rank Hchild_global Hchild_safe Hchild_fuel)
    as [child_required [Hchild_required Hchild_complete]].
  assert (Hchild_fit :
    phase1_surface_parser_local_measure input child_rank <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    eapply phase1_surface_same_input_measure_fits_parent_remaining.
    exact Hdecrease.
  }
  exists (S child_required).
  split.
  - unfold phase1_surface_parser_local_measure in *.
    lia.
  - intros extra.
    simpl.
    rewrite Hdecision.
    rewrite (Hchild_complete extra).
    reflexivity.
Qed.

Lemma phase1_surface_repetition_wrapper_bounded_complete :
  forall path body input rest trees,
    phase1_surface_parser_bounded_complete
      (GoalRepetition path body)
      input rest (ResultTrees trees) ->
    phase1_surface_parser_bounded_complete
      (GoalExpression path (ERepetition body))
      input rest (ResultTree (PTRepetition trees)).
Proof.
  intros path body input rest trees IHrepeat.
  unfold phase1_surface_parser_bounded_complete in IHrepeat |- *.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  unfold phase1_surface_parser_goal_rank_fuel in Hrank.
  destruct static_fuel as [| static_fuel]; try discriminate Hrank.
  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      static_fuel (GoalRepetition path body)).
  {
    eapply phase1_surface_repetition_wrapper_options_global.
    exact Hglobal.
  }
  assert (Hchild_safe :
    phase1_surface_parser_goal_choice_safe
      static_fuel (GoalRepetition path body)).
  {
    eapply phase1_surface_repetition_wrapper_choice_safe.
    exact Hsafe.
  }
  destruct
    (phase1_surface_parser_goal_rank_exists
      static_fuel (GoalRepetition path body) Hchild_global)
    as [child_rank Hchild_rank].
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < rank).
  {
    eapply parser_repetition_wrapper_rank_decreases; eauto.
  }
  assert (Hchild_fuel : static_fuel <= expression_fuel) by lia.
  destruct
    (IHrepeat
      static_fuel child_rank
      Hchild_rank Hchild_global Hchild_safe Hchild_fuel)
    as [child_required [Hchild_required Hchild_complete]].
  assert (Hchild_fit :
    phase1_surface_parser_local_measure input child_rank <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank).
  {
    eapply phase1_surface_same_input_measure_fits_parent_remaining.
    exact Hdecrease.
  }
  exists (S child_required).
  split.
  - unfold phase1_surface_parser_local_measure in *.
    lia.
  - intros extra.
    simpl.
    rewrite (Hchild_complete extra).
    reflexivity.
Qed.

Lemma phase1_surface_sequence_nil_bounded_complete :
  forall path index input,
    phase1_surface_parser_bounded_complete
      (GoalSequence path index [])
      input input (ResultTrees []).
Proof.
  intros path index input.
  unfold phase1_surface_parser_bounded_complete.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  exists 1.
  split.
  - unfold phase1_surface_parser_local_measure. lia.
  - intros extra.
    simpl.
    reflexivity.
Qed.

Lemma phase1_surface_repetition_stop_bounded_complete :
  forall path body input,
    phase1_surface_predictive_oracle path input = Some ChooseRepetitionStop ->
    phase1_surface_parser_bounded_complete
      (GoalRepetition path body)
      input input (ResultTrees []).
Proof.
  intros path body input Hdecision.
  unfold phase1_surface_parser_bounded_complete.
  intros static_fuel rank Hrank Hglobal Hsafe Hsfuel.
  exists 1.
  split.
  - unfold phase1_surface_parser_local_measure. lia.
  - intros extra.
    simpl.
    rewrite Hdecision.
    reflexivity.
Qed.

Theorem phase1_surface_oracle_parse_fuel_bounded_complete :
  forall goal input rest result,
    OracleDerives
      phase1_surface_predictive_oracle
      phase1_surface_rules
      goal input rest result ->
    forall static_fuel rank,
      phase1_surface_parser_goal_rank_fuel static_fuel goal = Some rank ->
      phase1_surface_parser_goal_options_global static_fuel goal ->
      phase1_surface_parser_goal_choice_safe static_fuel goal ->
      static_fuel <= expression_fuel ->
      exists required,
        required <= phase1_surface_parser_local_measure input rank /\
        forall extra,
          oracle_parse_fuel
            (required + extra)
            phase1_surface_predictive_oracle
            phase1_surface_rules
            goal input = Some (rest, result).
Proof.
  intros goal input rest result Hderive.
  change (phase1_surface_parser_bounded_complete goal input rest result).
  induction Hderive as
    [ path literal tail
    | path class lexeme tail
    | path name body input rest tree Hlookup Hbody IHbody
    | path items input rest trees Hitems IHitems
    | path items index item input rest tree Hdecision Hnth Hitem IHitem
    | path body input Hdecision
    | path body input rest tree Hdecision Hbody IHbody
    | path body input rest trees Hrepeat IHrepeat
    | path index input
    | path index item items input middle rest tree trees
        Hhead IHhead Htail IHtail
    | path body input Hdecision
    | path body input middle rest tree trees
        Hdecision Hbody IHbody Hprogress Htail IHtail
    ].
  - exact (phase1_surface_literal_bounded_complete path literal tail).
  - exact (phase1_surface_lexical_bounded_complete path class lexeme tail).
  - exact
      (phase1_surface_nonterminal_bounded_complete
        path name body input rest tree Hlookup IHbody).
  - exact
      (phase1_surface_sequence_wrapper_bounded_complete
        path items input rest trees IHitems).
  - exact
      (phase1_surface_alternative_bounded_complete
        path items index item input rest tree Hdecision Hnth IHitem).
  - exact
      (phase1_surface_optional_none_bounded_complete
        path body input Hdecision).
  - exact
      (phase1_surface_optional_some_bounded_complete
        path body input rest tree Hdecision IHbody).
  - exact
      (phase1_surface_repetition_wrapper_bounded_complete
        path body input rest trees IHrepeat).
  - exact
      (phase1_surface_sequence_nil_bounded_complete path index input).
  - exact
      (phase1_surface_sequence_cons_bounded_complete
        path index item items input middle rest tree trees
        Hhead IHhead Htail IHtail).
  - exact
      (phase1_surface_repetition_stop_bounded_complete
        path body input Hdecision).
  - exact
      (phase1_surface_repetition_step_bounded_complete
        path body input middle rest tree trees
        Hdecision Hbody IHbody Hprogress Htail IHtail).
Qed.

Theorem phase1_surface_predictive_parse_total_fuel_oracle_complete :
  forall tokens tree,
    OracleResolvedPhase1CompleteDerivation
      phase1_surface_predictive_oracle tokens tree ->
    phase1_surface_predictive_parse_fuel
      (phase1_surface_parser_total_fuel tokens) tokens =
      Some ([], ResultTree tree).
Proof.
  intros tokens tree Hderive.
  unfold OracleResolvedPhase1CompleteDerivation,
    OracleResolvedExpression in Hderive.
  destruct
    (phase1_surface_parser_goal_rank_exists
      expression_fuel
      (GoalExpression [] (ENonterminal phase1_surface_start))
      phase1_surface_root_goal_options_global)
    as [root_rank Hroot_rank].
  destruct
    (phase1_surface_oracle_parse_fuel_bounded_complete
      (GoalExpression [] (ENonterminal phase1_surface_start))
      tokens [] (ResultTree tree) Hderive
      expression_fuel root_rank Hroot_rank
      phase1_surface_root_goal_options_global
      phase1_surface_root_goal_choice_safe
      (Nat.le_refl _))
    as [required [Hrequired Hcomplete]].
  pose proof
    (phase1_surface_parser_goal_rank_below_global_bound
      expression_fuel
      (GoalExpression [] (ENonterminal phase1_surface_start))
      root_rank phase1_surface_root_goal_options_global Hroot_rank)
    as Hroot_bound.
  assert (Hlocal_total :
    phase1_surface_parser_local_measure tokens root_rank <=
      phase1_surface_parser_total_fuel tokens).
  {
    unfold phase1_surface_parser_local_measure,
      phase1_surface_parser_total_fuel.
    nia.
  }
  assert (Hrequired_total :
    required <= phase1_surface_parser_total_fuel tokens) by lia.
  unfold phase1_surface_predictive_parse_fuel.
  replace
    (phase1_surface_parser_total_fuel tokens)
    with
    (required + (phase1_surface_parser_total_fuel tokens - required))
    by lia.
  apply Hcomplete.
Qed.

Theorem phase1_surface_predictive_parse_total_fuel_complete :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    phase1_surface_predictive_parse_fuel
      (phase1_surface_parser_total_fuel tokens) tokens =
      Some ([], ResultTree tree).
Proof.
  intros tokens tree Hderive.
  apply phase1_surface_predictive_parse_total_fuel_oracle_complete.
  apply phase1_surface_complete_derivation_predictive_oracle.
  exact Hderive.
Qed.

Theorem phase1_surface_predictive_total_fuel_accepts_iff_derivable :
  forall tokens,
    (exists tree,
      phase1_surface_predictive_parse_fuel
        (phase1_surface_parser_total_fuel tokens) tokens =
        Some ([], ResultTree tree)) <->
    (exists tree, Phase1CompleteDerivation tokens tree).
Proof.
  intros tokens.
  split.
  - intros [tree Hparse].
    exists tree.
    eapply phase1_surface_predictive_parse_fuel_ordinary_sound.
    exact Hparse.
  - intros [tree Hderive].
    exists tree.
    eapply phase1_surface_predictive_parse_total_fuel_complete.
    exact Hderive.
Qed.