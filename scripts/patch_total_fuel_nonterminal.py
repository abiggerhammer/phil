from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuel.v")
text = path.read_text()

start_marker = "Lemma phase1_surface_nonterminal_bounded_sufficient :"
end_marker = "Lemma phase1_surface_sequence_wrapper_bounded_sufficient :"

if text.count(start_marker) != 1 or text.count(end_marker) != 1:
    raise SystemExit("could not uniquely locate nonterminal bounded-sufficient lemma")

start = text.index(start_marker)
end = text.index(end_marker, start)
segment = text[start:end]

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

for index, (old, new) in enumerate(replacements, start=1):
    count = segment.count(old)
    if count != 1:
        raise SystemExit(
            f"nonterminal replacement {index}: expected exactly one match, found {count}"
        )
    segment = segment.replace(old, new)

text = text[:start] + segment + text[end:]
path.write_text(text)
