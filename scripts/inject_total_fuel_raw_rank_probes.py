from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuelNonterminalBudget.v")
text = path.read_text()
marker = "Lemma phase1_surface_nonterminal_child_parse_from_budget :"

probes = r'''
(* Total-rank diagnostics.  Do not expose the concrete
   parser_expression_rank_fuel computation in any theorem interface: Rocq
   9.2 and 9.3-rc1 both spend >300s closing even tiny theorems that package
   that computation for an arbitrary rule body.  Instead recover the rule
   body's total parser_expression_rank from the stable rank table. *)

Lemma parser_rank_lookup_of_pass :
  forall rules facts name body,
    lookupRule name rules = Some body ->
    parser_rank_lookup name (parser_rank_pass rules facts) =
    parser_expression_rank facts body.
Proof.
  induction rules as [| [candidate candidate_body] rest IH];
    intros facts name body Hlookup.
  - simpl in Hlookup.
    discriminate.
  - simpl in Hlookup |- *.
    destruct (String.eqb name candidate) eqn:Hsame.
    + inversion Hlookup.
      subst body.
      reflexivity.
    + eapply IH.
      exact Hlookup.
Qed.

Lemma parser_rank_lookup_of_stable_pass :
  forall rules facts name body,
    parser_rank_pass rules facts = facts ->
    lookupRule name rules = Some body ->
    parser_rank_lookup name facts = parser_expression_rank facts body.
Proof.
  intros rules facts name body Hstable Hlookup.
  pose proof
    (parser_rank_lookup_of_pass rules facts name body Hlookup) as Hrank.
  rewrite Hstable in Hrank.
  exact Hrank.
Qed.

Lemma phase1_surface_lookup_rule_total_rank :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    parser_rank_lookup name phase1_surface_parser_rank_facts =
    parser_expression_rank phase1_surface_parser_rank_facts body.
Proof.
  intros name body Hlookup.
  eapply parser_rank_lookup_of_stable_pass.
  - exact phase1_surface_parser_rank_facts_are_stable.
  - exact Hlookup.
Qed.

Lemma phase1_surface_nonterminal_total_rank_decreases_probe :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    parser_expression_rank phase1_surface_parser_rank_facts body <
    parser_expression_rank
      phase1_surface_parser_rank_facts (ENonterminal name).
Proof.
  intros name body Hlookup.
  pose proof
    (phase1_surface_lookup_rule_total_rank name body Hlookup) as Hrank.
  change
    (parser_expression_rank phase1_surface_parser_rank_facts body <
      S (parser_rank_lookup name phase1_surface_parser_rank_facts)).
  rewrite Hrank.
  apply Nat.lt_succ_diag_r.
Qed.

Lemma phase1_surface_nonterminal_total_rank_budget_probe :
  forall path name body input rest tree,
    lookupRule name phase1_surface_rules = Some body ->
    (forall budget,
      phase1_surface_parser_local_measure
        input
        (parser_expression_rank phase1_surface_parser_rank_facts body) <=
      budget ->
      oracle_parse_fuel
        budget
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression (descend path (AtNonterminal name)) body)
        input = Some (rest, ResultTree tree)) ->
    forall budget,
      phase1_surface_parser_local_measure
        input
        (parser_expression_rank
          phase1_surface_parser_rank_facts (ENonterminal name)) <=
      budget ->
      oracle_parse_fuel
        budget
        phase1_surface_predictive_oracle
        phase1_surface_rules
        (GoalExpression path (ENonterminal name))
        input = Some (rest, ResultTree (PTNonterminal name tree)).
Proof.
  intros path name body input rest tree Hlookup IHbody budget Hbudget.
  destruct budget as [| remaining].
  - unfold phase1_surface_parser_local_measure in Hbudget.
    lia.
  - assert (Hdecrease :
      parser_expression_rank phase1_surface_parser_rank_facts body <
      parser_expression_rank
        phase1_surface_parser_rank_facts (ENonterminal name)) by
      abstract (
        eapply phase1_surface_nonterminal_total_rank_decreases_probe;
        exact Hlookup).
    assert (Hchild_fit :
      phase1_surface_parser_local_measure
        input
        (parser_expression_rank phase1_surface_parser_rank_facts body) <=
      remaining) by
      abstract (
        unfold phase1_surface_parser_local_measure in *;
        lia).
    pose proof (IHbody remaining Hchild_fit) as Hchild_parse.
    eapply oracle_parse_fuel_nonterminal_success.
    + exact Hlookup.
    + exact Hchild_parse.
Qed.

'''

if marker not in text:
    raise SystemExit(f"marker not found in {path}")
path.write_text(text.replace(marker, probes + marker, 1))
