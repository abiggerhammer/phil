From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyMutualPredictiveBridge
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyPredictiveOracle
  GrammarParserGoalRank
  GrammarParserGlobalGoalRank
  GrammarParserProgress
  GrammarParserRecognizer
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
  Kernel-friendly total-fuel completeness.

  The previous proof carried equations of the form

    phase1_surface_parser_goal_rank_fuel fuel goal = Some rank

  through the recursive theorem interface.  Rocq 9.2 and 9.3-rc1 both exhibit
  pathological proof-term closure on the concrete Grammar-v1 nonterminal
  transport for that representation.  This proof carries only the value of
  the same certified computation.  Structural recursive calls lower static
  fuel; nonterminal expansion resets it to expression_fuel.  No concrete rank
  equality crosses an induction boundary.
*)

Definition phase1_surface_rank_value (value : option nat) : nat :=
  match value with
  | Some rank => rank
  | None => 0
  end.

Definition phase1_surface_parser_goal_rank_value
  (fuel : nat)
  (goal : DerivationGoal) : nat :=
  phase1_surface_rank_value
    (phase1_surface_parser_goal_rank_fuel fuel goal).

Definition phase1_surface_parser_value_measure
  (input : list ConcreteToken)
  (rank : nat) : nat :=
  S
    (List.length input * phase1_surface_parser_global_goal_rank_bound +
     rank).

Lemma phase1_surface_value_same_input_fits_remaining :
  forall input child_rank parent_rank remaining,
    child_rank < parent_rank ->
    phase1_surface_parser_value_measure input parent_rank <= S remaining ->
    phase1_surface_parser_value_measure input child_rank <= remaining.
Proof.
  intros input child_rank parent_rank remaining Hrank Hparent.
  unfold phase1_surface_parser_value_measure in *.
  lia.
Qed.

Lemma phase1_surface_value_progress_fits_remaining :
  forall (input middle : list ConcreteToken) child_rank parent_rank remaining,
    List.length middle < List.length input ->
    child_rank < phase1_surface_parser_global_goal_rank_bound ->
    phase1_surface_parser_value_measure input parent_rank <= S remaining ->
    phase1_surface_parser_value_measure middle child_rank <= remaining.
Proof.
  intros input middle child_rank parent_rank remaining Hlength Hrank Hparent.
  pose proof phase1_surface_parser_global_goal_rank_bound_positive as Hpositive.
  unfold phase1_surface_parser_value_measure in *.
  nia.
Qed.

Lemma phase1_surface_goal_rank_value_below_global_bound :
  forall fuel goal,
    phase1_surface_parser_goal_options_global fuel goal ->
    phase1_surface_parser_goal_rank_value fuel goal <
      phase1_surface_parser_global_goal_rank_bound.
Proof.
  intros fuel goal Hglobal.
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  destruct (phase1_surface_parser_goal_rank_fuel fuel goal)
    as [rank |] eqn:Hrank.
  - eapply phase1_surface_parser_goal_rank_below_global_bound; eauto.
  - exact phase1_surface_parser_global_goal_rank_bound_positive.
Qed.

Lemma phase1_surface_nonterminal_rank_value_decreases :
  forall static_fuel path name body,
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_parser_goal_options_global
      static_fuel (GoalExpression path (ENonterminal name)) ->
    phase1_surface_parser_goal_rank_value
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body) <
    phase1_surface_parser_goal_rank_value
      static_fuel
      (GoalExpression path (ENonterminal name)).
Proof.
  intros static_fuel path name body Hlookup Hglobal.
  destruct static_fuel as [| fuel].
  - destruct
      (phase1_surface_parser_goal_rank_exists
        0 (GoalExpression path (ENonterminal name)) Hglobal)
      as [rank Hrank].
    discriminate Hrank.
  - unfold phase1_surface_parser_goal_rank_value,
      phase1_surface_rank_value,
      phase1_surface_parser_goal_rank_fuel.
    simpl.
    change
      (parser_expression_rank phase1_surface_parser_rank_facts body <
       S (parser_rank_lookup name phase1_surface_parser_rank_facts)).
    eapply parser_nonterminal_child_rank_decreases.
    exact Hlookup.
Qed.

Lemma phase1_surface_sequence_wrapper_rank_value_decreases :
  forall fuel path items,
    phase1_surface_parser_goal_options_global
      (S fuel) (GoalExpression path (ESequence items)) ->
    phase1_surface_parser_goal_rank_value
      fuel (GoalSequence path 0 items) <
    phase1_surface_parser_goal_rank_value
      (S fuel) (GoalExpression path (ESequence items)).
Proof.
  intros fuel path items Hglobal.
  destruct
    (phase1_surface_parser_goal_rank_exists
      (S fuel) (GoalExpression path (ESequence items)) Hglobal)
    as [parent_rank Hparent].
  pose proof
    (phase1_surface_sequence_wrapper_options_global
      fuel path items Hglobal) as Hchild_global.
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalSequence path 0 items) Hchild_global)
    as [child_rank Hchild].
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  rewrite Hparent, Hchild.
  simpl.
  unfold phase1_surface_parser_goal_rank_fuel in Hparent, Hchild.
  eapply parser_sequence_wrapper_rank_decreases; eauto.
Qed.

Lemma phase1_surface_alternative_rank_value_decreases :
  forall fuel path items index item,
    nth_error items index = Some item ->
    phase1_surface_parser_goal_options_global
      (S fuel) (GoalExpression path (EAlternative items)) ->
    phase1_surface_parser_goal_rank_value
      fuel (GoalExpression (descend path (AtAlternative index)) item) <
    phase1_surface_parser_goal_rank_value
      (S fuel) (GoalExpression path (EAlternative items)).
Proof.
  intros fuel path items index item Hnth Hglobal.
  pose proof
    (phase1_surface_alternative_member_options_global
      fuel path items index item Hnth Hglobal) as Hchild_global.
  destruct
    (phase1_surface_parser_goal_rank_exists
      (S fuel) (GoalExpression path (EAlternative items)) Hglobal)
    as [parent_rank Hparent].
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalExpression (descend path (AtAlternative index)) item)
      Hchild_global)
    as [item_rank Hitem].
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  rewrite Hparent, Hitem.
  simpl.
  unfold phase1_surface_parser_goal_rank_fuel in Hparent, Hitem.
  rewrite parser_expression_alternative_rank_equation in Hparent.
  destruct (parser_alternative_goal_rank_fuel
      fuel phase1_surface_parser_rank_facts items)
    as [alternative_rank |] eqn:Halternative; try discriminate Hparent.
  inversion Hparent; subst parent_rank.
  pose proof
    (parser_alternative_member_rank_le
      fuel phase1_surface_parser_rank_facts
      items index item alternative_rank item_rank
      Hnth Halternative Hitem) as Hle.
  lia.
Qed.

Lemma phase1_surface_optional_rank_value_decreases :
  forall fuel path body,
    phase1_surface_parser_goal_options_global
      (S fuel) (GoalExpression path (EOptional body)) ->
    phase1_surface_parser_goal_rank_value
      fuel (GoalExpression (descend path AtOptionalBody) body) <
    phase1_surface_parser_goal_rank_value
      (S fuel) (GoalExpression path (EOptional body)).
Proof.
  intros fuel path body Hglobal.
  pose proof
    (phase1_surface_optional_body_options_global fuel path body Hglobal)
    as Hchild_global.
  destruct
    (phase1_surface_parser_goal_rank_exists
      (S fuel) (GoalExpression path (EOptional body)) Hglobal)
    as [parent_rank Hparent].
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalExpression (descend path AtOptionalBody) body)
      Hchild_global)
    as [body_rank Hbody].
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  rewrite Hparent, Hbody.
  simpl.
  unfold phase1_surface_parser_goal_rank_fuel in Hparent, Hbody.
  eapply parser_optional_body_rank_decreases; eauto.
Qed.

Lemma phase1_surface_repetition_wrapper_rank_value_decreases :
  forall fuel path body,
    phase1_surface_parser_goal_options_global
      (S fuel) (GoalExpression path (ERepetition body)) ->
    phase1_surface_parser_goal_rank_value
      fuel (GoalRepetition path body) <
    phase1_surface_parser_goal_rank_value
      (S fuel) (GoalExpression path (ERepetition body)).
Proof.
  intros fuel path body Hglobal.
  pose proof
    (phase1_surface_repetition_wrapper_options_global
      fuel path body Hglobal) as Hchild_global.
  destruct
    (phase1_surface_parser_goal_rank_exists
      (S fuel) (GoalExpression path (ERepetition body)) Hglobal)
    as [parent_rank Hparent].
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalRepetition path body) Hchild_global)
    as [repeat_rank Hrepeat].
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  rewrite Hparent, Hrepeat.
  simpl.
  unfold phase1_surface_parser_goal_rank_fuel in Hparent, Hrepeat.
  eapply parser_repetition_wrapper_rank_decreases; eauto.
Qed.

Lemma phase1_surface_sequence_head_rank_value_decreases :
  forall fuel path index item rest,
    phase1_surface_parser_goal_options_global
      fuel (GoalSequence path index (item :: rest)) ->
    phase1_surface_parser_goal_rank_value
      fuel (GoalExpression (descend path (AtSequence index)) item) <
    phase1_surface_parser_goal_rank_value
      fuel (GoalSequence path index (item :: rest)).
Proof.
  intros fuel path index item rest Hglobal.
  pose proof
    (phase1_surface_sequence_head_options_global
      fuel path index item rest Hglobal) as Hhead_global.
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalSequence path index (item :: rest)) Hglobal)
    as [sequence_rank Hsequence].
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalExpression (descend path (AtSequence index)) item)
      Hhead_global)
    as [head_rank Hhead].
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  rewrite Hsequence, Hhead.
  simpl.
  unfold phase1_surface_parser_goal_rank_fuel in Hsequence, Hhead.
  eapply parser_sequence_head_rank_decreases; eauto.
Qed.

Lemma phase1_surface_sequence_tail_rank_value_decreases :
  forall fuel path index item rest,
    nullable_expression phase1_surface_nullable_facts item = true ->
    phase1_surface_parser_goal_options_global
      fuel (GoalSequence path index (item :: rest)) ->
    phase1_surface_parser_goal_rank_value
      fuel (GoalSequence path (S index) rest) <
    phase1_surface_parser_goal_rank_value
      fuel (GoalSequence path index (item :: rest)).
Proof.
  intros fuel path index item rest Hnullable Hglobal.
  pose proof
    (phase1_surface_sequence_tail_options_global
      fuel path index item rest Hglobal) as Htail_global.
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalSequence path index (item :: rest)) Hglobal)
    as [sequence_rank Hsequence].
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalSequence path (S index) rest) Htail_global)
    as [tail_rank Htail].
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  rewrite Hsequence, Htail.
  simpl.
  unfold phase1_surface_parser_goal_rank_fuel in Hsequence, Htail.
  eapply parser_sequence_nullable_tail_rank_decreases; eauto.
Qed.

Lemma phase1_surface_repetition_body_rank_value_decreases :
  forall fuel path body,
    phase1_surface_parser_goal_options_global
      fuel (GoalRepetition path body) ->
    phase1_surface_parser_goal_rank_value
      fuel (GoalExpression (descend path AtRepetitionBody) body) <
    phase1_surface_parser_goal_rank_value
      fuel (GoalRepetition path body).
Proof.
  intros fuel path body Hglobal.
  pose proof
    (phase1_surface_repetition_body_options_global
      fuel path body Hglobal) as Hbody_global.
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalRepetition path body) Hglobal)
    as [repeat_rank Hrepeat].
  destruct
    (phase1_surface_parser_goal_rank_exists
      fuel (GoalExpression (descend path AtRepetitionBody) body)
      Hbody_global)
    as [body_rank Hbody].
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  rewrite Hrepeat, Hbody.
  simpl.
  unfold phase1_surface_parser_goal_rank_fuel in Hrepeat, Hbody.
  eapply parser_repetition_body_rank_decreases; eauto.
Qed.

Theorem phase1_surface_oracle_parse_budget_complete_value :
  forall goal input rest result,
    OracleDerives
      phase1_surface_predictive_oracle
      phase1_surface_rules
      goal input rest result ->
    forall static_fuel budget,
      phase1_surface_parser_goal_options_global static_fuel goal ->
      phase1_surface_parser_goal_choice_safe static_fuel goal ->
      static_fuel <= expression_fuel ->
      phase1_surface_parser_value_measure
        input (phase1_surface_parser_goal_rank_value static_fuel goal) <=
      budget ->
      oracle_parse_fuel
        budget
        phase1_surface_predictive_oracle
        phase1_surface_rules
        goal input = Some (rest, result).
Proof.
  intros goal input rest result Hderive.
  induction Hderive as
    [ path literal tail
    | path class lexeme tail
    | path name body input rest tree Hlookup Hbody IHbody
    | path items input rest trees Hsequence IHsequence
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
    ];
    intros static_fuel budget Hglobal Hsafe Hsfuel Hbudget.
  - destruct budget as [| remaining].
    + unfold phase1_surface_parser_value_measure in Hbudget. lia.
    + simpl. rewrite String.eqb_refl. reflexivity.
  - destruct budget as [| remaining].
    + unfold phase1_surface_parser_value_measure in Hbudget. lia.
    + simpl. rewrite String.eqb_refl. reflexivity.
  - destruct budget as [| remaining].
    + unfold phase1_surface_parser_value_measure in Hbudget. lia.
    + assert (Hchild_global :
        phase1_surface_parser_goal_options_global
          expression_fuel
          (GoalExpression (descend path (AtNonterminal name)) body)).
      {
        eapply phase1_surface_lookup_rule_goal_options_global.
        exact Hlookup.
      }
      assert (Hchild_safe :
        phase1_surface_parser_goal_choice_safe
          expression_fuel
          (GoalExpression (descend path (AtNonterminal name)) body)).
      {
        constructor.
        unfold phase1_surface_parser_goal_choice_safe_structural.
        apply phase1_surface_expression_choice_safe_of_bool.
        eapply phase1_surface_lookup_rule_choice_safe.
        exact Hlookup.
      }
      assert (Hdecrease :
        phase1_surface_parser_goal_rank_value
          expression_fuel
          (GoalExpression (descend path (AtNonterminal name)) body) <
        phase1_surface_parser_goal_rank_value
          static_fuel
          (GoalExpression path (ENonterminal name))).
      {
        eapply phase1_surface_nonterminal_rank_value_decreases; eauto.
      }
      assert (Hchild_fit :
        phase1_surface_parser_value_measure
          input
          (phase1_surface_parser_goal_rank_value
            expression_fuel
            (GoalExpression (descend path (AtNonterminal name)) body)) <=
        remaining).
      {
        eapply phase1_surface_value_same_input_fits_remaining; eauto.
      }
      pose proof
        (IHbody
          expression_fuel remaining
          Hchild_global Hchild_safe (Nat.le_refl _) Hchild_fit)
        as Hchild_parse.
      simpl.
      rewrite Hlookup, Hchild_parse.
      reflexivity.
  - destruct static_fuel as [| fuel].
    + destruct
        (phase1_surface_parser_goal_rank_exists
          0 (GoalExpression path (ESequence items)) Hglobal)
        as [rank Hrank].
      discriminate Hrank.
    + destruct budget as [| remaining].
      * unfold phase1_surface_parser_value_measure in Hbudget. lia.
      * pose proof
          (phase1_surface_sequence_wrapper_options_global
            fuel path items Hglobal) as Hchild_global.
        pose proof
          (phase1_surface_sequence_wrapper_choice_safe
            fuel path items Hsafe) as Hchild_safe.
        assert (Hdecrease :
          phase1_surface_parser_goal_rank_value
            fuel (GoalSequence path 0 items) <
          phase1_surface_parser_goal_rank_value
            (S fuel) (GoalExpression path (ESequence items))).
        {
          eapply phase1_surface_sequence_wrapper_rank_value_decreases.
          exact Hglobal.
        }
        assert (Hchild_fit :
          phase1_surface_parser_value_measure
            input
            (phase1_surface_parser_goal_rank_value
              fuel (GoalSequence path 0 items)) <= remaining).
        {
          eapply phase1_surface_value_same_input_fits_remaining; eauto.
        }
        assert (Hchild_fuel : fuel <= expression_fuel) by lia.
        pose proof
          (IHsequence fuel remaining
            Hchild_global Hchild_safe Hchild_fuel Hchild_fit)
          as Hchild_parse.
        simpl.
        rewrite Hchild_parse.
        reflexivity.
  - destruct static_fuel as [| fuel].
    + destruct
        (phase1_surface_parser_goal_rank_exists
          0 (GoalExpression path (EAlternative items)) Hglobal)
        as [rank Hrank].
      discriminate Hrank.
    + destruct budget as [| remaining].
      * unfold phase1_surface_parser_value_measure in Hbudget. lia.
      * pose proof
          (phase1_surface_alternative_member_options_global
            fuel path items index item Hnth Hglobal) as Hchild_global.
        pose proof
          (phase1_surface_alternative_member_choice_safe
            fuel path items index item Hnth Hsafe) as Hchild_safe.
        assert (Hdecrease :
          phase1_surface_parser_goal_rank_value
            fuel (GoalExpression (descend path (AtAlternative index)) item) <
          phase1_surface_parser_goal_rank_value
            (S fuel) (GoalExpression path (EAlternative items))).
        {
          eapply phase1_surface_alternative_rank_value_decreases; eauto.
        }
        assert (Hchild_fit :
          phase1_surface_parser_value_measure
            input
            (phase1_surface_parser_goal_rank_value
              fuel
              (GoalExpression (descend path (AtAlternative index)) item)) <=
          remaining).
        {
          eapply phase1_surface_value_same_input_fits_remaining; eauto.
        }
        assert (Hchild_fuel : fuel <= expression_fuel) by lia.
        pose proof
          (IHitem fuel remaining
            Hchild_global Hchild_safe Hchild_fuel Hchild_fit)
          as Hchild_parse.
        simpl.
        rewrite Hdecision, Hnth, Hchild_parse.
        reflexivity.
  - destruct budget as [| remaining].
    + unfold phase1_surface_parser_value_measure in Hbudget. lia.
    + simpl. rewrite Hdecision. reflexivity.
  - destruct static_fuel as [| fuel].
    + destruct
        (phase1_surface_parser_goal_rank_exists
          0 (GoalExpression path (EOptional body)) Hglobal)
        as [rank Hrank].
      discriminate Hrank.
    + destruct budget as [| remaining].
      * unfold phase1_surface_parser_value_measure in Hbudget. lia.
      * pose proof
          (phase1_surface_optional_body_options_global
            fuel path body Hglobal) as Hchild_global.
        pose proof
          (phase1_surface_optional_body_choice_safe
            fuel path body Hsafe) as Hchild_safe.
        assert (Hdecrease :
          phase1_surface_parser_goal_rank_value
            fuel (GoalExpression (descend path AtOptionalBody) body) <
          phase1_surface_parser_goal_rank_value
            (S fuel) (GoalExpression path (EOptional body))).
        {
          eapply phase1_surface_optional_rank_value_decreases.
          exact Hglobal.
        }
        assert (Hchild_fit :
          phase1_surface_parser_value_measure
            input
            (phase1_surface_parser_goal_rank_value
              fuel (GoalExpression (descend path AtOptionalBody) body)) <=
          remaining).
        {
          eapply phase1_surface_value_same_input_fits_remaining; eauto.
        }
        assert (Hchild_fuel : fuel <= expression_fuel) by lia.
        pose proof
          (IHbody fuel remaining
            Hchild_global Hchild_safe Hchild_fuel Hchild_fit)
          as Hchild_parse.
        simpl.
        rewrite Hdecision, Hchild_parse.
        reflexivity.
  - destruct static_fuel as [| fuel].
    + destruct
        (phase1_surface_parser_goal_rank_exists
          0 (GoalExpression path (ERepetition body)) Hglobal)
        as [rank Hrank].
      discriminate Hrank.
    + destruct budget as [| remaining].
      * unfold phase1_surface_parser_value_measure in Hbudget. lia.
      * pose proof
          (phase1_surface_repetition_wrapper_options_global
            fuel path body Hglobal) as Hchild_global.
        pose proof
          (phase1_surface_repetition_wrapper_choice_safe
            fuel path body Hsafe) as Hchild_safe.
        assert (Hdecrease :
          phase1_surface_parser_goal_rank_value
            fuel (GoalRepetition path body) <
          phase1_surface_parser_goal_rank_value
            (S fuel) (GoalExpression path (ERepetition body))).
        {
          eapply phase1_surface_repetition_wrapper_rank_value_decreases.
          exact Hglobal.
        }
        assert (Hchild_fit :
          phase1_surface_parser_value_measure
            input
            (phase1_surface_parser_goal_rank_value
              fuel (GoalRepetition path body)) <= remaining).
        {
          eapply phase1_surface_value_same_input_fits_remaining; eauto.
        }
        assert (Hchild_fuel : fuel <= expression_fuel) by lia.
        pose proof
          (IHrepeat fuel remaining
            Hchild_global Hchild_safe Hchild_fuel Hchild_fit)
          as Hchild_parse.
        simpl.
        rewrite Hchild_parse.
        reflexivity.
  - destruct budget as [| remaining].
    + unfold phase1_surface_parser_value_measure in Hbudget. lia.
    + simpl. reflexivity.
  - destruct budget as [| remaining].
    + unfold phase1_surface_parser_value_measure in Hbudget. lia.
    + destruct
        (phase1_surface_sequence_cons_choice_safe
          static_fuel path index item items Hsafe)
        as [Hhead_safe Htail_safe].
      pose proof
        (phase1_surface_sequence_head_options_global
          static_fuel path index item items Hglobal) as Hhead_global.
      pose proof
        (phase1_surface_sequence_tail_options_global
          static_fuel path index item items Hglobal) as Htail_global.
      assert (Hhead_decrease :
        phase1_surface_parser_goal_rank_value
          static_fuel
          (GoalExpression (descend path (AtSequence index)) item) <
        phase1_surface_parser_goal_rank_value
          static_fuel (GoalSequence path index (item :: items))).
      {
        eapply phase1_surface_sequence_head_rank_value_decreases.
        exact Hglobal.
      }
      assert (Hhead_fit :
        phase1_surface_parser_value_measure
          input
          (phase1_surface_parser_goal_rank_value
            static_fuel
            (GoalExpression (descend path (AtSequence index)) item)) <=
        remaining).
      {
        eapply phase1_surface_value_same_input_fits_remaining; eauto.
      }
      pose proof
        (IHhead static_fuel remaining
          Hhead_global Hhead_safe Hsfuel Hhead_fit) as Hhead_parse.
      assert (Htail_fit :
        phase1_surface_parser_value_measure
          middle
          (phase1_surface_parser_goal_rank_value
            static_fuel (GoalSequence path (S index) items)) <=
        remaining).
      {
        destruct (list_eq_dec concrete_token_eq_dec input middle)
          as [Hequal | Hdifferent].
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
          assert (Htail_decrease :
            phase1_surface_parser_goal_rank_value
              static_fuel (GoalSequence path (S index) items) <
            phase1_surface_parser_goal_rank_value
              static_fuel (GoalSequence path index (item :: items))).
          {
            eapply phase1_surface_sequence_tail_rank_value_decreases; eauto.
          }
          eapply phase1_surface_value_same_input_fits_remaining; eauto.
        - pose proof
            (oracle_derivation_progress_decreases_length
              phase1_surface_predictive_oracle
              phase1_surface_rules
              (GoalExpression (descend path (AtSequence index)) item)
              input middle (ResultTree tree) Hhead Hdifferent)
            as Hlength.
          pose proof
            (phase1_surface_goal_rank_value_below_global_bound
              static_fuel (GoalSequence path (S index) items) Htail_global)
            as Htail_bound.
          eapply phase1_surface_value_progress_fits_remaining; eauto.
      }
      pose proof
        (IHtail static_fuel remaining
          Htail_global Htail_safe Hsfuel Htail_fit) as Htail_parse.
      simpl.
      rewrite Hhead_parse, Htail_parse.
      reflexivity.
  - destruct budget as [| remaining].
    + unfold phase1_surface_parser_value_measure in Hbudget. lia.
    + simpl. rewrite Hdecision. reflexivity.
  - destruct budget as [| remaining].
    + unfold phase1_surface_parser_value_measure in Hbudget. lia.
    + pose proof
        (phase1_surface_repetition_body_options_global
          static_fuel path body Hglobal) as Hbody_global.
      pose proof
        (phase1_surface_repetition_body_choice_safe
          static_fuel path body Hsafe) as Hbody_safe.
      assert (Hbody_decrease :
        phase1_surface_parser_goal_rank_value
          static_fuel (GoalExpression (descend path AtRepetitionBody) body) <
        phase1_surface_parser_goal_rank_value
          static_fuel (GoalRepetition path body)).
      {
        eapply phase1_surface_repetition_body_rank_value_decreases.
        exact Hglobal.
      }
      assert (Hbody_fit :
        phase1_surface_parser_value_measure
          input
          (phase1_surface_parser_goal_rank_value
            static_fuel
            (GoalExpression (descend path AtRepetitionBody) body)) <=
        remaining).
      {
        eapply phase1_surface_value_same_input_fits_remaining; eauto.
      }
      pose proof
        (IHbody static_fuel remaining
          Hbody_global Hbody_safe Hsfuel Hbody_fit) as Hbody_parse.
      pose proof
        (oracle_derivation_progress_decreases_length
          phase1_surface_predictive_oracle
          phase1_surface_rules
          (GoalExpression (descend path AtRepetitionBody) body)
          input middle (ResultTree tree) Hbody Hprogress)
        as Hlength.
      pose proof
        (phase1_surface_goal_rank_value_below_global_bound
          static_fuel (GoalRepetition path body) Hglobal) as Htail_bound.
      assert (Htail_fit :
        phase1_surface_parser_value_measure
          middle
          (phase1_surface_parser_goal_rank_value
            static_fuel (GoalRepetition path body)) <= remaining).
      {
        eapply phase1_surface_value_progress_fits_remaining; eauto.
      }
      pose proof
        (IHtail static_fuel remaining
          Hglobal Hsafe Hsfuel Htail_fit) as Htail_parse.
      simpl.
      rewrite Hdecision, Hbody_parse.
      destruct (list_eq_dec concrete_token_eq_dec input middle)
        as [Hequal | Hdifferent].
      * exfalso. apply Hprogress. exact Hequal.
      * rewrite Htail_parse. reflexivity.
Qed.

Theorem phase1_surface_predictive_parse_total_fuel_oracle_complete_value :
  forall tokens tree,
    OracleResolvedPhase1CompleteDerivation
      phase1_surface_predictive_oracle tokens tree ->
    phase1_surface_predictive_parse_fuel
      (phase1_surface_parser_total_fuel tokens) tokens =
      Some ([], ResultTree tree).
Proof.
  intros tokens tree Hderive.
  pose proof phase1_surface_root_goal_options_global as Hglobal.
  pose proof phase1_surface_root_goal_choice_safe as Hsafe.
  pose proof
    (phase1_surface_goal_rank_value_below_global_bound
      expression_fuel
      (GoalExpression [] (ENonterminal phase1_surface_start))
      Hglobal) as Hrank_bound.
  assert (Hmeasure :
    phase1_surface_parser_value_measure
      tokens
      (phase1_surface_parser_goal_rank_value
        expression_fuel
        (GoalExpression [] (ENonterminal phase1_surface_start))) <=
    phase1_surface_parser_total_fuel tokens).
  {
    unfold phase1_surface_parser_value_measure,
      phase1_surface_parser_total_fuel.
    nia.
  }
  unfold OracleResolvedPhase1CompleteDerivation in Hderive.
  unfold OracleResolvedExpression in Hderive.
  unfold phase1_surface_predictive_parse_fuel.
  eapply phase1_surface_oracle_parse_budget_complete_value;
    eauto using Nat.le_refl.
Qed.

Theorem phase1_surface_predictive_parse_total_fuel_complete_value :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    phase1_surface_predictive_parse_fuel
      (phase1_surface_parser_total_fuel tokens) tokens =
      Some ([], ResultTree tree).
Proof.
  intros tokens tree Hderive.
  apply phase1_surface_predictive_parse_total_fuel_oracle_complete_value.
  apply phase1_surface_complete_derivation_predictive_oracle.
  exact Hderive.
Qed.
