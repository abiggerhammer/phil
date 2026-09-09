from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuelStatementProbe.v")
path.write_text(r'''From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyPredictiveOracle
  GrammarParserGlobalGoalRank
  GrammarParserRecognizer
  GrammarParserTotalFuelBase
  GrammarParserTotalFuelStatic.

Import ListNotations.
Open Scope string_scope.

Opaque phase1_surface_rules
  phase1_surface_parser_global_goal_rank_bound
  phase1_surface_predictive_oracle.

Definition phase1_surface_child_budget_claim
  (path : DerivationPath)
  (name : string)
  (body : EbnfExpression)
  (input rest : list ConcreteToken)
  (tree : ParseTree) : Prop :=
  forall static_fuel rank budget,
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
      input = Some (rest, ResultTree tree).

Definition phase1_surface_parent_budget_claim
  (path : DerivationPath)
  (name : string)
  (input rest : list ConcreteToken)
  (tree : ParseTree) : Prop :=
  forall static_fuel rank budget,
    phase1_surface_parser_goal_rank_fuel
      static_fuel (GoalExpression path (ENonterminal name)) =
      Some rank ->
    phase1_surface_parser_goal_options_global
      static_fuel (GoalExpression path (ENonterminal name)) ->
    phase1_surface_parser_goal_choice_safe
      static_fuel (GoalExpression path (ENonterminal name)) ->
    static_fuel <= expression_fuel ->
    phase1_surface_parser_local_measure input rank <= budget ->
    oracle_parse_fuel
      budget
      phase1_surface_predictive_oracle
      phase1_surface_rules
      (GoalExpression path (ENonterminal name))
      input = Some (rest, ResultTree (PTNonterminal name tree)).

Lemma phase1_surface_parent_budget_claim_identity :
  forall path name input rest tree,
    phase1_surface_parent_budget_claim path name input rest tree ->
    phase1_surface_parent_budget_claim path name input rest tree.
Proof.
  intros path name input rest tree Hparent.
  exact Hparent.
Qed.

Lemma phase1_surface_nonterminal_budget_statement_identity :
  forall path name body input rest tree,
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_child_budget_claim path name body input rest tree ->
    phase1_surface_parent_budget_claim path name input rest tree ->
    phase1_surface_parent_budget_claim path name input rest tree.
Proof.
  intros path name body input rest tree Hlookup Hchild Hparent.
  exact Hparent.
Qed.

Lemma phase1_surface_nonterminal_budget_raw_identity :
  forall path name body input rest tree,
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
    (forall static_fuel rank budget,
      phase1_surface_parser_goal_rank_fuel
        static_fuel (GoalExpression path (ENonterminal name)) =
        Some rank ->
      phase1_surface_parser_goal_options_global
        static_fuel (GoalExpression path (ENonterminal name)) ->
      phase1_surface_parser_goal_choice_safe
        static_fuel (GoalExpression path (ENonterminal name)) ->
      static_fuel <= expression_fuel ->
      phase1_surface_parser_local_measure input rank <= budget ->
      oracle_parse_fuel
        budget
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression path (ENonterminal name))
        input = Some (rest, ResultTree (PTNonterminal name tree))) ->
    forall static_fuel rank budget,
      phase1_surface_parser_goal_rank_fuel
        static_fuel (GoalExpression path (ENonterminal name)) =
        Some rank ->
      phase1_surface_parser_goal_options_global
        static_fuel (GoalExpression path (ENonterminal name)) ->
      phase1_surface_parser_goal_choice_safe
        static_fuel (GoalExpression path (ENonterminal name)) ->
      static_fuel <= expression_fuel ->
      phase1_surface_parser_local_measure input rank <= budget ->
      oracle_parse_fuel
        budget
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression path (ENonterminal name))
        input = Some (rest, ResultTree (PTNonterminal name tree)).
Proof.
  intros path name body input rest tree Hlookup Hchild Hparent.
  exact Hparent.
Qed.
''')
