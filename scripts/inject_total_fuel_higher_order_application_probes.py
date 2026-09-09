from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuelNonterminalBudget.v")
text = path.read_text()
marker = "Lemma phase1_surface_nonterminal_child_parse_from_budget :"

probes = r'''
(* Diagnostic ladder: isolate whether closing a direct application of the
   recursive budget hypothesis is itself pathological, or whether one of the
   locally derived child facts is required to trigger the blow-up. *)

Lemma phase1_surface_budget_hypothesis_apply_supplied :
  forall path name body input rest tree child_rank remaining,
    (forall static_fuel rank budget,
      phase1_surface_parser_goal_rank_fuel
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) =
        Some rank ->
      phase1_surface_parser_goal_options_global
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      phase1_surface_parser_goal_choice_safe
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      static_fuel <= expression_fuel ->
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
    phase1_surface_parser_goal_options_global
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body) ->
    phase1_surface_parser_goal_choice_safe
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body) ->
    phase1_surface_parser_local_measure input child_rank <= remaining ->
    oracle_parse_fuel
      remaining
      phase1_surface_predictive_oracle
      phase1_surface_rules
      (GoalExpression (descend path (AtNonterminal name)) body)
      input = Some (rest, ResultTree tree).
Proof.
  intros path name body input rest tree child_rank remaining
    IHbody Hchild_rank Hchild_global Hchild_safe Hchild_fit.
  exact
    (IHbody
      expression_fuel child_rank remaining
      Hchild_rank Hchild_global Hchild_safe
      (Nat.le_refl _) Hchild_fit).
Qed.

Lemma phase1_surface_budget_hypothesis_apply_lookup_derived :
  forall path name body input rest tree child_rank remaining,
    lookupRule name phase1_surface_rules = Some body ->
    (forall static_fuel rank budget,
      phase1_surface_parser_goal_rank_fuel
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) =
        Some rank ->
      phase1_surface_parser_goal_options_global
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      phase1_surface_parser_goal_choice_safe
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      static_fuel <= expression_fuel ->
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
    phase1_surface_parser_local_measure input child_rank <= remaining ->
    oracle_parse_fuel
      remaining
      phase1_surface_predictive_oracle
      phase1_surface_rules
      (GoalExpression (descend path (AtNonterminal name)) body)
      input = Some (rest, ResultTree tree).
Proof.
  intros path name body input rest tree child_rank remaining
    Hlookup IHbody Hchild_rank Hchild_fit.
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
  exact
    (IHbody
      expression_fuel child_rank remaining
      Hchild_rank Hchild_global Hchild_safe
      (Nat.le_refl _) Hchild_fit).
Qed.

Lemma phase1_surface_budget_hypothesis_apply_fit_derived :
  forall path name body input rest tree child_rank parent_rank remaining,
    lookupRule name phase1_surface_rules = Some body ->
    (forall static_fuel rank budget,
      phase1_surface_parser_goal_rank_fuel
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) =
        Some rank ->
      phase1_surface_parser_goal_options_global
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      phase1_surface_parser_goal_choice_safe
        static_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) ->
      static_fuel <= expression_fuel ->
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
    child_rank < parent_rank ->
    phase1_surface_parser_local_measure input parent_rank <= S remaining ->
    oracle_parse_fuel
      remaining
      phase1_surface_predictive_oracle
      phase1_surface_rules
      (GoalExpression (descend path (AtNonterminal name)) body)
      input = Some (rest, ResultTree tree).
Proof.
  intros path name body input rest tree child_rank parent_rank remaining
    Hlookup IHbody Hchild_rank Hdecrease Hbudget.
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
