from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuel.v")
text = path.read_text()

start_marker = "Lemma phase1_surface_nonterminal_bounded_sufficient :"
end_marker = "Lemma phase1_surface_sequence_wrapper_bounded_sufficient :"

if text.count(start_marker) != 1 or text.count(end_marker) != 1:
    raise SystemExit("could not uniquely locate nonterminal bounded-sufficient lemma")

start = text.index(start_marker)
end = text.index(end_marker, start)

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

expression_goal_rank_helper = '''Lemma phase1_surface_expression_goal_rank_from_raw :
  forall fuel path expression rank,
    parser_expression_rank_fuel
      fuel phase1_surface_parser_rank_facts expression = Some rank ->
    phase1_surface_parser_goal_rank_fuel
      fuel (GoalExpression path expression) = Some rank.
Proof.
  intros fuel path expression rank Hrank.
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
    parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body =
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
    Hlookup Hdecrease IHbody Hchild_rank_raw Hchild_global Hchild_safe.
  pose proof
    (phase1_surface_expression_goal_rank_from_raw
      expression_fuel
      (descend path (AtNonterminal name))
      body child_rank Hchild_rank_raw) as Hchild_rank.
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

payload_helper = '''Lemma phase1_surface_nonterminal_bounded_payload :
  forall path name body input rest tree,
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_parser_bounded_sufficient
      (GoalExpression (descend path (AtNonterminal name)) body)
      input rest (ResultTree tree) ->
    forall static_fuel rank,
      phase1_surface_parser_goal_rank_fuel
        static_fuel (GoalExpression path (ENonterminal name)) = Some rank ->
      phase1_surface_parser_goal_options_global
        static_fuel (GoalExpression path (ENonterminal name)) ->
      phase1_surface_parser_goal_choice_safe
        static_fuel (GoalExpression path (ENonterminal name)) ->
      static_fuel <= expression_fuel ->
      exists required,
        required <= phase1_surface_parser_local_measure input rank /\\
        OracleParseFuelSufficient
          phase1_surface_predictive_oracle
          phase1_surface_rules
          (GoalExpression path (ENonterminal name))
          input rest (ResultTree (PTNonterminal name tree)) required.
Proof.
  intros path name body input rest tree Hlookup IHbody
    static_fuel rank Hrank Hglobal Hsafe Hsfuel.
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
  pose proof
    (phase1_surface_lookup_rule_rank_fuel_sufficient
      name body Hlookup) as Hchild_defined.
  unfold parser_rank_rule_fuel_sufficient in Hchild_defined.
  destruct
    (parser_expression_rank_fuel
      expression_fuel phase1_surface_parser_rank_facts body)
    as [child_rank |] eqn:Hchild_rank_raw.
  - assert (Hdecrease : child_rank < rank) by
      abstract (
        eapply phase1_surface_nonterminal_child_rank_decreases_fuel;
        eauto).
    eapply phase1_surface_nonterminal_required_lift.
    + exact Hlookup.
    + exact Hdecrease.
    + exact IHbody.
    + exact Hchild_rank_raw.
    + exact Hchild_global.
    + exact Hchild_safe.
  - simpl in Hchild_defined.
    discriminate.
Qed.

'''

wrapper_helper = '''Lemma phase1_surface_nonterminal_bounded_sufficient :
  forall path name body input rest tree,
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_parser_bounded_sufficient
      (GoalExpression (descend path (AtNonterminal name)) body)
      input rest (ResultTree tree) ->
    phase1_surface_parser_bounded_sufficient
      (GoalExpression path (ENonterminal name))
      input rest (ResultTree (PTNonterminal name tree)).
Proof.
  intros path name body input rest tree Hlookup IHbody.
  constructor.
  eapply phase1_surface_nonterminal_bounded_payload.
  - exact Hlookup.
  - exact IHbody.
Qed.

'''

replacement = (
    lookup_member_helper
    + rank_sufficient_helper
    + expression_goal_rank_helper
    + required_helper
    + payload_helper
    + wrapper_helper
)

text = text[:start] + replacement + text[end:]
path.write_text(text)
