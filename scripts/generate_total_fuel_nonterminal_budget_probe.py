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
  GrammarParserTotalFuelNonterminalSupport
  GrammarParserTotalFuelStatic.

Import ListNotations.
Open Scope string_scope.

Opaque phase1_surface_rules
  phase1_surface_nullable_facts
  phase1_surface_parser_rank_facts
  phase1_surface_parser_global_goal_rank_bound
  phase1_surface_predictive_oracle.

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
  pose proof
    (phase1_surface_lookup_rule_rank_fuel_sufficient
      name body Hlookup) as Hchild_defined.
  unfold parser_rank_rule_fuel_sufficient in Hchild_defined.
  destruct
    (parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body)
    as [child_rank |] eqn:Hchild_rank_raw.
  - assert (Hdecrease : child_rank < rank).
    {
      eapply phase1_surface_nonterminal_child_rank_decreases_fuel; eauto.
    }
    destruct budget as [| remaining].
    + unfold phase1_surface_parser_local_measure in Hbudget.
      lia.
    + assert (Hchild_rank :
        phase1_surface_parser_goal_rank_fuel
          expression_fuel
          (GoalExpression (descend path (AtNonterminal name)) body) =
        Some child_rank).
      {
        eapply phase1_surface_expression_goal_rank_from_raw.
        exact Hchild_rank_raw.
      }
      assert (Hchild_fit :
        phase1_surface_parser_local_measure input child_rank <= remaining).
      {
        unfold phase1_surface_parser_local_measure in *.
        lia.
      }
      pose proof
        (IHbody
          expression_fuel child_rank remaining
          Hchild_rank Hchild_global Hchild_safe
          (Nat.le_refl _) Hchild_fit) as Hchild_parse.
      simpl.
      rewrite Hlookup.
      rewrite Hchild_parse.
      reflexivity.
  - simpl in Hchild_defined.
    discriminate.
Qed.
''')
