from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuel.v")
text = path.read_text()

replacements = [
    (
        '''  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)).
  {
    eapply phase1_surface_lookup_rule_goal_options_global.
    exact Hlookup.
  }
''',
        '''  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)) by
    abstract (
      eapply phase1_surface_lookup_rule_goal_options_global;
      exact Hlookup).
''',
    ),
    (
        '''  assert (Hchild_safe :
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
''',
        '''  assert (Hchild_safe :
    phase1_surface_parser_goal_choice_safe
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)) by
    abstract (
      constructor;
      unfold phase1_surface_parser_goal_choice_safe_structural;
      apply phase1_surface_expression_choice_safe_of_bool;
      eapply phase1_surface_lookup_rule_choice_safe;
      exact Hlookup).
''',
    ),
    (
        '''  assert (Hdecrease : child_rank < rank).
  {
    eapply phase1_surface_nonterminal_child_rank_decreases_fuel; eauto.
  }
''',
        '''  assert (Hdecrease : child_rank < rank) by
    abstract (
      eapply phase1_surface_nonterminal_child_rank_decreases_fuel;
      eauto).
''',
    ),
    (
        '''  assert (Hchild_fit :
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
''',
        '''  assert (Hchild_fit :
    phase1_surface_parser_local_measure input child_rank <=
      List.length input * phase1_surface_parser_global_goal_rank_bound + rank) by
    abstract (
      eapply phase1_surface_same_input_measure_fits_parent_remaining;
      exact Hdecrease).
  assert (Hrequired_bound :
    S child_required <= phase1_surface_parser_local_measure input rank) by
    abstract (
      unfold phase1_surface_parser_local_measure in *;
      lia).
  exists (S child_required).
  split.
  - exact Hrequired_bound.
''',
    ),
]

for old, new in replacements:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected exactly one match, found {count}")
    text = text.replace(old, new)

path.write_text(text)
