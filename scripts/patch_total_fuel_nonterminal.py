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

canonical_helper = '''Lemma phase1_surface_expression_goal_canonical_rank :
  forall path expression,
    phase1_surface_parser_goal_options_global
      expression_fuel (GoalExpression path expression) ->
    phase1_surface_parser_goal_rank_fuel
      expression_fuel (GoalExpression path expression) =
    Some
      (parser_expression_rank
        phase1_surface_parser_rank_facts expression).
Proof.
  intros path expression Hglobal.
  destruct
    (phase1_surface_parser_goal_rank_exists
      expression_fuel (GoalExpression path expression) Hglobal)
    as [rank Hrank].
  pose proof Hrank as Hraw.
  unfold phase1_surface_parser_goal_rank_fuel in Hraw.
  pose proof
    (parser_expression_rank_of_fuel_some
      phase1_surface_parser_rank_facts expression rank Hraw) as Hequal.
  rewrite Hequal.
  exact Hrank.
Qed.

'''

required_helper = '''Lemma phase1_surface_nonterminal_required_lift :
  forall path name body input rest tree child_rank rank,
    lookupRule name phase1_surface_rules = Some body ->
    child_rank < rank ->
    phase1_surface_parser_bounded_sufficient
      (GoalExpression (descend path (AtNonterminal name)) body)
      input rest (ResultTree tree) ->
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
    exists required,
      required <= phase1_surface_parser_local_measure input rank /\\
      OracleParseFuelSufficient
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression path (ENonterminal name))
        input rest (ResultTree (PTNonterminal name tree)) required.
Proof.
  intros path name body input rest tree child_rank rank
    Hlookup Hdecrease IHbody Hchild_rank Hchild_global Hchild_safe.
  destruct
    (phase1_surface_parser_bounded_sufficient_elim
      (GoalExpression (descend path (AtNonterminal name)) body)
      input rest (ResultTree tree) IHbody
      expression_fuel child_rank
      Hchild_rank Hchild_global Hchild_safe (Nat.le_refl _))
    as [child_required [Hchild_required Hchild_sufficient]].
  exists (S child_required).
  split.
  - unfold phase1_surface_parser_local_measure in *.
    lia.
  - eapply FuelNonterminal.
    + exact Hlookup.
    + exact Hchild_sufficient.
Qed.

'''

prefix = ""
if "Lemma phase1_surface_expression_goal_canonical_rank :" not in text:
    prefix += canonical_helper
if "Lemma phase1_surface_nonterminal_required_lift :" not in text:
    prefix += required_helper
if prefix:
    text = text[:start] + prefix + text[start:]
    start += len(prefix)
    end += len(prefix)
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
        '''  destruct
    (phase1_surface_parser_goal_rank_exists
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)
      Hchild_global)
    as [child_rank Hchild_rank].
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < rank).
  {
    eapply phase1_surface_nonterminal_child_rank_decreases_fuel; eauto.
  }
''',
        '''  set
    (child_rank :=
      parser_expression_rank phase1_surface_parser_rank_facts body).
  assert (Hchild_rank :
    phase1_surface_parser_goal_rank_fuel
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body) =
    Some child_rank) by
    abstract (
      unfold child_rank;
      eapply phase1_surface_expression_goal_canonical_rank;
      exact Hchild_global).
  pose proof Hchild_rank as Hchild_rank_raw.
  unfold phase1_surface_parser_goal_rank_fuel in Hchild_rank_raw.
  assert (Hdecrease : child_rank < rank) by
    abstract (
      eapply phase1_surface_nonterminal_child_rank_decreases_fuel;
      eauto).
''',
    ),
    (
        '''  destruct
    (phase1_surface_parser_bounded_sufficient_elim
      (GoalExpression (descend path (AtNonterminal name)) body)
      input rest (ResultTree tree) IHbody
      expression_fuel child_rank
      Hchild_rank Hchild_global Hchild_safe (Nat.le_refl _))
    as [child_required [Hchild_required Hchild_sufficient]].
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
  - eapply FuelNonterminal.
    + exact Hlookup.
    + exact Hchild_sufficient.
Qed.

''',
        '''  eapply phase1_surface_nonterminal_required_lift.
  - exact Hlookup.
  - exact Hdecrease.
  - exact IHbody.
  - exact Hchild_rank.
  - exact Hchild_global.
  - exact Hchild_safe.
Qed.

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
