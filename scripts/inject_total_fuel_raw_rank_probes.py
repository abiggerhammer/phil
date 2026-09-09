from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuelNonterminalBudget.v")
text = path.read_text()
marker = "Lemma phase1_surface_nonterminal_child_parse_from_budget :"

probes = r'''
(* Raw-rank diagnostics.  Goal-rank -> expression-rank conversion is the
   minimal closure pathology isolated by the preceding probes.  Keep the
   recursive hypothesis and both rank equations entirely in the raw
   parser_expression_rank_fuel representation and test the complete
   nonterminal child/parent budget step on that side of the boundary. *)

Lemma phase1_surface_lookup_rule_raw_rank_exists_probe :
  forall (path : SyntaxPath) name body,
    lookupRule name phase1_surface_rules = Some body ->
    exists rank,
      parser_expression_rank_fuel
        expression_fuel phase1_surface_parser_rank_facts body = Some rank.
Proof.
  intros path name body Hlookup.
  pose proof
    (phase1_surface_lookup_rule_rank_fuel_sufficient
      name body Hlookup) as Hdefined.
  unfold parser_rank_rule_fuel_sufficient in Hdefined.
  destruct
    (parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body)
    as [rank |] eqn:Hrank.
  - exists rank.
    exact Hrank.
  - simpl in Hdefined.
    discriminate.
Qed.

Lemma phase1_surface_raw_rank_budget_hypothesis_apply_supplied :
  forall path name body input rest tree child_rank parent_rank remaining fuel,
    lookupRule name phase1_surface_rules = Some body ->
    (forall child_static_fuel rank budget,
      parser_expression_rank_fuel
        child_static_fuel phase1_surface_parser_rank_facts body =
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
    parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body =
      Some child_rank ->
    parser_expression_rank_fuel
      (S fuel) phase1_surface_parser_rank_facts (ENonterminal name) =
      Some parent_rank ->
    phase1_surface_parser_local_measure input parent_rank <= S remaining ->
    oracle_parse_fuel
      remaining
      phase1_surface_predictive_oracle
      phase1_surface_rules
      (GoalExpression (descend path (AtNonterminal name)) body)
      input = Some (rest, ResultTree tree).
Proof.
  intros path name body input rest tree child_rank parent_rank remaining fuel
    Hlookup IHbody Hchild_rank Hparent_rank Hbudget.
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

Lemma phase1_surface_raw_rank_budget_hypothesis_apply_child_derived :
  forall path name body input rest tree parent_rank remaining fuel,
    lookupRule name phase1_surface_rules = Some body ->
    (forall child_static_fuel rank budget,
      parser_expression_rank_fuel
        child_static_fuel phase1_surface_parser_rank_facts body =
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
    parser_expression_rank_fuel
      (S fuel) phase1_surface_parser_rank_facts (ENonterminal name) =
      Some parent_rank ->
    phase1_surface_parser_local_measure input parent_rank <= S remaining ->
    oracle_parse_fuel
      remaining
      phase1_surface_predictive_oracle
      phase1_surface_rules
      (GoalExpression (descend path (AtNonterminal name)) body)
      input = Some (rest, ResultTree tree).
Proof.
  intros path name body input rest tree parent_rank remaining fuel
    Hlookup IHbody Hparent_rank Hbudget.
  destruct
    (phase1_surface_lookup_rule_raw_rank_exists_probe
      path name body Hlookup) as [child_rank Hchild_rank].
  eapply phase1_surface_raw_rank_budget_hypothesis_apply_supplied;
    eauto.
Qed.

Lemma phase1_surface_nonterminal_raw_rank_budget_complete_probe :
  forall path name body input rest tree,
    lookupRule name phase1_surface_rules = Some body ->
    (forall child_static_fuel rank budget,
      parser_expression_rank_fuel
        child_static_fuel phase1_surface_parser_rank_facts body =
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
    forall fuel rank budget,
      parser_expression_rank_fuel
        (S fuel) phase1_surface_parser_rank_facts (ENonterminal name) =
        Some rank ->
      phase1_surface_parser_local_measure input rank <= budget ->
      oracle_parse_fuel
        budget
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression path (ENonterminal name))
        input = Some (rest, ResultTree (PTNonterminal name tree)).
Proof.
  intros path name body input rest tree Hlookup IHbody
    fuel rank budget Hrank Hbudget.
  destruct budget as [| remaining].
  - unfold phase1_surface_parser_local_measure in Hbudget.
    lia.
  - pose proof
      (phase1_surface_raw_rank_budget_hypothesis_apply_child_derived
        path name body input rest tree rank remaining fuel
        Hlookup IHbody Hrank Hbudget) as Hchild_parse.
    eapply oracle_parse_fuel_nonterminal_success.
    + exact Hlookup.
    + exact Hchild_parse.
Qed.

'''

if marker not in text:
    raise SystemExit(f"marker not found in {path}")
path.write_text(text.replace(marker, probes + marker, 1))
