from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuelNonterminalBudget.v")
text = path.read_text()
marker = "Lemma phase1_surface_nonterminal_child_parse_from_budget :"

probes = r'''
(* Rank-path diagnostics.  The preceding higher-order application probes show
   that the recursive budget hypothesis itself, lookup-derived global/safety
   facts, and locally derived fit arithmetic all seal quickly.  These two
   probes split the remaining rank-selection/decrease block. *)

Lemma phase1_surface_budget_hypothesis_apply_decrease_derived :
  forall path name body input rest tree child_rank parent_rank remaining static_fuel,
    lookupRule name phase1_surface_rules = Some body ->
    (forall child_static_fuel rank budget,
      phase1_surface_parser_goal_rank_fuel
        child_static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) =
        Some rank ->
      phase1_surface_parser_goal_options_global
        child_static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      phase1_surface_parser_goal_choice_safe
        child_static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      child_static_fuel <= expression_fuel ->
      phase1_surface_parser_local_measure input rank <= budget ->
      oracle_parse_fuel
        budget
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression (descend path (AtNonterminal name)) body)
        input = Some (rest, ResultTree tree)) ->
    phase1_surface_parser_goal_rank_fuel
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body) =
      Some child_rank ->
    phase1_surface_parser_goal_rank_fuel
      static_fuel (GoalExpression path (ENonterminal name)) =
      Some parent_rank ->
    phase1_surface_parser_local_measure input parent_rank <= S remaining ->
    oracle_parse_fuel
      remaining
      phase1_surface_predictive_oracle
      phase1_surface_rules
      (GoalExpression (descend path (AtNonterminal name)) body)
      input = Some (rest, ResultTree tree).
Proof.
  intros path name body input rest tree child_rank parent_rank remaining static_fuel
    Hlookup IHbody Hchild_rank Hrank Hbudget.
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
  unfold phase1_surface_parser_goal_rank_fuel in Hrank.
  destruct static_fuel as [| static_fuel]; try discriminate Hrank.
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < parent_rank) by
    abstract (
      eapply phase1_surface_nonterminal_child_rank_decreases_fuel;
      eauto).
  assert (Hchild_fit :
    phase1_surface_parser_local_measure input child_rank <= remaining) by
    abstract (
      unfold phase1_surface_parser_local_measure in *;
      lia).
  exact
    (IHbody
      expression_fuel child_rank remaining
      Hchild_rank Hchild_global Hchild_safe
      (Nat.le_refl _) Hchild_fit).
Qed.

Lemma phase1_surface_budget_hypothesis_apply_rank_exists :
  forall path name body input rest tree parent_rank remaining static_fuel,
    lookupRule name phase1_surface_rules = Some body ->
    (forall child_static_fuel rank budget,
      phase1_surface_parser_goal_rank_fuel
        child_static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) =
        Some rank ->
      phase1_surface_parser_goal_options_global
        child_static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      phase1_surface_parser_goal_choice_safe
        child_static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      child_static_fuel <= expression_fuel ->
      phase1_surface_parser_local_measure input rank <= budget ->
      oracle_parse_fuel
        budget
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression (descend path (AtNonterminal name)) body)
        input = Some (rest, ResultTree tree)) ->
    phase1_surface_parser_goal_rank_fuel
      static_fuel (GoalExpression path (ENonterminal name)) =
      Some parent_rank ->
    phase1_surface_parser_local_measure input parent_rank <= S remaining ->
    oracle_parse_fuel
      remaining
      phase1_surface_predictive_oracle
      phase1_surface_rules
      (GoalExpression (descend path (AtNonterminal name)) body)
      input = Some (rest, ResultTree tree).
Proof.
  intros path name body input rest tree parent_rank remaining static_fuel
    Hlookup IHbody Hrank Hbudget.
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
  unfold phase1_surface_parser_goal_rank_fuel in Hrank.
  destruct static_fuel as [| static_fuel]; try discriminate Hrank.
  assert (Hchild_rank_exists :
    exists child_rank,
      phase1_surface_parser_goal_rank_fuel
        expression_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) =
        Some child_rank).
  {
    eapply phase1_surface_parser_goal_rank_exists.
    exact Hchild_global.
  }
  destruct Hchild_rank_exists as [child_rank Hchild_rank].
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < parent_rank) by
    abstract (
      eapply phase1_surface_nonterminal_child_rank_decreases_fuel;
      eauto).
  assert (Hchild_fit :
    phase1_surface_parser_local_measure input child_rank <= remaining) by
    abstract (
      unfold phase1_surface_parser_local_measure in *;
      lia).
  exact
    (IHbody
      expression_fuel child_rank remaining
      Hchild_rank Hchild_global Hchild_safe
      (Nat.le_refl _) Hchild_fit).
Qed.

'''

if marker not in text:
    raise SystemExit(f"marker not found in {path}")
path.write_text(text.replace(marker, probes + marker, 1))
