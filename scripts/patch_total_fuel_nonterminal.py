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

lookup_member_helper = '''Lemma lookup_rule_member :
  forall rules name body,
    lookupRule name rules = Some body ->
    In (name, body) rules.
Proof.
  induction rules as [| [candidate expression] rest IH];
    intros name body Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (String.eqb name candidate) eqn:Hname.
    + apply String.eqb_eq in Hname.
      subst candidate.
      inversion Hlookup.
      subst body.
      left.
      reflexivity.
    + right.
      eapply IH.
      exact Hlookup.
Qed.

'''

rank_sufficient_helper = '''Lemma phase1_surface_lookup_rule_rank_fuel_sufficient :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    parser_rank_rule_fuel_sufficient (name, body) = true.
Proof.
  intros name body Hlookup.
  pose proof
    phase1_surface_parser_rank_expression_fuel_is_sufficient as Hall.
  rewrite forallb_forall in Hall.
  apply Hall.
  eapply lookup_rule_member.
  exact Hlookup.
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

prefix = lookup_member_helper + rank_sufficient_helper + required_helper
text = text[:start] + prefix + text[start:]
start += len(prefix)
end += len(prefix)
segment = text[start:end]

old_global = '''  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)).
  {
    eapply phase1_surface_lookup_rule_goal_options_global.
    exact Hlookup.
  }
'''
new_global = '''  assert (Hchild_global :
    phase1_surface_parser_goal_options_global
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)) by
    abstract (
      eapply phase1_surface_lookup_rule_goal_options_global;
      exact Hlookup).
'''

old_safe = '''  assert (Hchild_safe :
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
'''
new_safe = '''  assert (Hchild_safe :
    phase1_surface_parser_goal_choice_safe
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body)) by
    abstract (
      constructor;
      unfold phase1_surface_parser_goal_choice_safe_structural;
      apply phase1_surface_expression_choice_safe_of_bool;
      eapply phase1_surface_lookup_rule_choice_safe;
      exact Hlookup).
'''

for label, old, new in [
    ("global", old_global, new_global),
    ("safe", old_safe, new_safe),
]:
    count = segment.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {count}")
    segment = segment.replace(old, new)

rank_start_marker = "  destruct\n    (phase1_surface_parser_goal_rank_exists"
rank_start = segment.index(rank_start_marker)
rank_end = segment.index("Qed.\n\n", rank_start) + len("Qed.\n\n")

new_tail = '''  pose proof
    (phase1_surface_lookup_rule_rank_fuel_sufficient
      name body Hlookup) as Hchild_defined.
  unfold parser_rank_rule_fuel_sufficient in Hchild_defined.
  destruct
    (parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body)
    as [child_rank |] eqn:Hchild_rank_raw.
  - assert (Hchild_rank :
      phase1_surface_parser_goal_rank_fuel
        expression_fuel
        (GoalExpression (descend path (AtNonterminal name)) body) =
      Some child_rank) by
      abstract (
        unfold phase1_surface_parser_goal_rank_fuel;
        exact Hchild_rank_raw).
    assert (Hdecrease : child_rank < rank) by
      abstract (
        eapply phase1_surface_nonterminal_child_rank_decreases_fuel;
        eauto).
    eapply phase1_surface_nonterminal_required_lift.
    + exact Hlookup.
    + exact Hdecrease.
    + exact IHbody.
    + exact Hchild_rank.
    + exact Hchild_global.
    + exact Hchild_safe.
  - simpl in Hchild_defined.
    discriminate.
Qed.

'''

segment = segment[:rank_start] + new_tail + segment[rank_end:]
text = text[:start] + segment + text[end:]
path.write_text(text)
