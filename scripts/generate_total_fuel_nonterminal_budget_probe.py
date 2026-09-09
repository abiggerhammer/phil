from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuelNonterminalBudget.v")
path.write_text(r'''From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyPredictiveOracle
  GrammarParserGoalRank
  GrammarParserGlobalGoalRank
  GrammarParserRank
  GrammarParserRecognizer
  GrammarParserTotalFuelBase
  GrammarParserTotalFuelStatic.

Import ListNotations.
Open Scope string_scope.

Opaque phase1_surface_rules
  phase1_surface_nullable_facts
  phase1_surface_parser_rank_facts
  phase1_surface_parser_global_goal_rank_bound
  phase1_surface_predictive_oracle.

Definition option_nat_value (value : option nat) : nat :=
  match value with
  | Some result => result
  | None => 0
  end.

Lemma option_nat_value_some_of_exists :
  forall value : option nat,
    (exists result, value = Some result) ->
    value = Some (option_nat_value value).
Proof.
  intros value [result Hvalue].
  rewrite Hvalue.
  reflexivity.
Qed.

Lemma oracle_parse_fuel_nonterminal_success :
  forall remaining oracle rules path name body input rest tree,
    lookupRule name rules = Some body ->
    oracle_parse_fuel
      remaining oracle rules
      (GoalExpression (descend path (AtNonterminal name)) body)
      input = Some (rest, ResultTree tree) ->
    oracle_parse_fuel
      (S remaining) oracle rules
      (GoalExpression path (ENonterminal name))
      input = Some (rest, ResultTree (PTNonterminal name tree)).
Proof.
  intros remaining oracle rules path name body input rest tree
    Hlookup Hchild.
  simpl.
  rewrite Hlookup.
  rewrite Hchild.
  reflexivity.
Qed.

Definition phase1_surface_parser_budget_complete
  (goal : DerivationGoal)
  (input rest : list ConcreteToken)
  (result : DerivationResult) : Prop :=
  forall static_fuel rank budget,
    phase1_surface_parser_goal_rank_fuel static_fuel goal = Some rank ->
    phase1_surface_parser_goal_options_global static_fuel goal ->
    phase1_surface_parser_goal_choice_safe static_fuel goal ->
    static_fuel <= expression_fuel ->
    phase1_surface_parser_local_measure input rank <= budget ->
    oracle_parse_fuel
      budget
      phase1_surface_predictive_oracle
      phase1_surface_rules
      goal input = Some (rest, result).

Lemma phase1_surface_nonterminal_budget_complete :
  forall path name body input rest tree,
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_parser_budget_complete
      (GoalExpression (descend path (AtNonterminal name)) body)
      input rest (ResultTree tree) ->
    phase1_surface_parser_budget_complete
      (GoalExpression path (ENonterminal name))
      input rest (ResultTree (PTNonterminal name tree)).
Proof.
  intros path name body input rest tree Hlookup IHbody.
  unfold phase1_surface_parser_budget_complete in *.
  intros static_fuel rank budget Hrank Hglobal Hsafe Hsfuel Hbudget.
  unfold phase1_surface_parser_goal_rank_fuel in Hrank.
  destruct static_fuel as [| static_fuel]; try discriminate Hrank.
  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)) by
    abstract (
      eapply phase1_surface_lookup_rule_goal_options_global;
      exact Hlookup).
  assert (Hchild_safe :
    phase1_surface_parser_goal_choice_safe
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)) by
    abstract (
      constructor;
      unfold phase1_surface_parser_goal_choice_safe_structural;
      apply phase1_surface_expression_choice_safe_of_bool;
      eapply phase1_surface_lookup_rule_choice_safe;
      exact Hlookup).
  set (child_goal :=
    GoalExpression (descend path (AtNonterminal name)) body).
  set (child_rank :=
    option_nat_value
      (phase1_surface_parser_goal_rank_fuel expression_fuel child_goal)).
  assert (Hchild_rank :
    phase1_surface_parser_goal_rank_fuel expression_fuel child_goal =
    Some child_rank) by
    abstract (
      subst child_rank;
      eapply option_nat_value_some_of_exists;
      eapply phase1_surface_parser_goal_rank_exists;
      subst child_goal;
      exact Hchild_global).
  pose proof Hchild_rank as Hchild_rank_raw.
  subst child_goal.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < rank) by
    abstract (
      eapply phase1_surface_nonterminal_child_rank_decreases_fuel;
      eauto).
  destruct budget as [| remaining].
  - unfold phase1_surface_parser_local_measure in Hbudget.
    lia.
  - assert (Hchild_fit :
      phase1_surface_parser_local_measure input child_rank <= remaining) by
      abstract (
        unfold phase1_surface_parser_local_measure in *;
        lia).
    assert (Hchild_parse :
      oracle_parse_fuel
        remaining
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression (descend path (AtNonterminal name)) body)
        input = Some (rest, ResultTree tree)) by
      abstract (
        exact
          (IHbody
            expression_fuel child_rank remaining
            Hchild_rank Hchild_global Hchild_safe
            (Nat.le_refl _) Hchild_fit)).
    assert (Hparent_parse :
      oracle_parse_fuel
        (S remaining)
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression path (ENonterminal name))
        input = Some (rest, ResultTree (PTNonterminal name tree))) by
      abstract (
        eapply oracle_parse_fuel_nonterminal_success;
        [exact Hlookup | exact Hchild_parse]).
    exact Hparent_parse.
Qed.
''')
