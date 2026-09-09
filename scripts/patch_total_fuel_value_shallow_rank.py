from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuelValue.v")
text = path.read_text()

old_def = r'''Definition phase1_surface_parser_goal_rank_value
  (fuel : nat)
  (goal : DerivationGoal) : nat :=
  phase1_surface_rank_value
    (phase1_surface_parser_goal_rank_fuel fuel goal).
'''

new_def = r'''Definition phase1_surface_parser_goal_rank_value
  (fuel : nat)
  (goal : DerivationGoal) : nat :=
  match goal with
  | GoalExpression _ expression =>
      match fuel with
      | 0 => 0
      | S remaining =>
          match expression with
          | ELiteral _ => 1
          | ELexicalClass _ => 1
          | ENonterminal name =>
              S (parser_rank_lookup name phase1_surface_parser_rank_facts)
          | ESequence items =>
              match
                parser_sequence_goal_rank_fuel
                  remaining phase1_surface_parser_rank_facts items
              with
              | Some rank => S rank
              | None => 0
              end
          | EAlternative items =>
              match
                parser_alternative_goal_rank_fuel
                  remaining phase1_surface_parser_rank_facts items
              with
              | Some rank => S rank
              | None => 0
              end
          | EOptional body =>
              match
                parser_expression_rank_fuel
                  remaining phase1_surface_parser_rank_facts body
              with
              | Some rank => S rank
              | None => 0
              end
          | ERepetition body =>
              match
                parser_expression_rank_fuel
                  remaining phase1_surface_parser_rank_facts body
              with
              | Some rank => S (S rank)
              | None => 0
              end
          end
      end
  | GoalSequence _ _ items =>
      phase1_surface_rank_value
        (parser_sequence_goal_rank_fuel
          fuel phase1_surface_parser_rank_facts items)
  | GoalRepetition _ body =>
      phase1_surface_rank_value
        (parser_repetition_goal_rank_fuel
          fuel phase1_surface_parser_rank_facts body)
  end.

Lemma phase1_surface_parser_goal_rank_value_equation :
  forall fuel goal,
    phase1_surface_parser_goal_rank_value fuel goal =
    phase1_surface_rank_value
      (phase1_surface_parser_goal_rank_fuel fuel goal).
Proof.
  intros fuel goal.
  destruct goal as [path expression | path index items | path body].
  - destruct fuel as [| fuel].
    + reflexivity.
    + destruct expression as
        [literal | class | name | items | items | body | body].
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * unfold phase1_surface_parser_goal_rank_fuel.
        simpl [phase1_surface_parser_goal_rank_value].
        rewrite parser_expression_sequence_rank_equation.
        destruct
          (parser_sequence_goal_rank_fuel
            fuel phase1_surface_parser_rank_facts items);
          reflexivity.
      * unfold phase1_surface_parser_goal_rank_fuel.
        simpl [phase1_surface_parser_goal_rank_value].
        rewrite parser_expression_alternative_rank_equation.
        destruct
          (parser_alternative_goal_rank_fuel
            fuel phase1_surface_parser_rank_facts items);
          reflexivity.
      * unfold phase1_surface_parser_goal_rank_fuel.
        simpl [phase1_surface_parser_goal_rank_value].
        destruct
          (parser_expression_rank_fuel
            fuel phase1_surface_parser_rank_facts body);
          reflexivity.
      * unfold phase1_surface_parser_goal_rank_fuel.
        simpl [phase1_surface_parser_goal_rank_value].
        destruct
          (parser_expression_rank_fuel
            fuel phase1_surface_parser_rank_facts body);
          reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma phase1_surface_expression_rank_value_at_expression_fuel :
  forall path expression,
    phase1_surface_parser_goal_rank_value
      expression_fuel (GoalExpression path expression) =
    parser_expression_rank phase1_surface_parser_rank_facts expression.
Proof.
  intros path expression.
  rewrite phase1_surface_parser_goal_rank_value_equation.
  unfold phase1_surface_parser_goal_rank_fuel,
    parser_expression_rank.
  reflexivity.
Qed.
'''

if old_def not in text:
    raise SystemExit("goal-rank value definition not found")
text = text.replace(old_def, new_def, 1)

old_bound = r'''Proof.
  intros fuel goal Hglobal.
  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
  destruct (phase1_surface_parser_goal_rank_fuel fuel goal)
    as [rank |] eqn:Hrank.
'''
new_bound = r'''Proof.
  intros fuel goal Hglobal.
  rewrite phase1_surface_parser_goal_rank_value_equation.
  unfold phase1_surface_rank_value.
  destruct (phase1_surface_parser_goal_rank_fuel fuel goal)
    as [rank |] eqn:Hrank.
'''
if old_bound not in text:
    raise SystemExit("global bound proof prefix not found")
text = text.replace(old_bound, new_bound, 1)

start = text.index("Lemma phase1_surface_nonterminal_rank_value_decreases :")
end = text.index("\nLemma phase1_surface_sequence_wrapper_rank_value_decreases :", start)
nonterminal = r'''Lemma phase1_surface_nonterminal_rank_value_decreases :
  forall static_fuel path name body,
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_parser_goal_options_global
      static_fuel (GoalExpression path (ENonterminal name)) ->
    phase1_surface_parser_goal_rank_value
      expression_fuel
      (GoalExpression (descend path (AtNonterminal name)) body) <
    phase1_surface_parser_goal_rank_value
      static_fuel
      (GoalExpression path (ENonterminal name)).
Proof.
  intros static_fuel path name body Hlookup Hglobal.
  destruct static_fuel as [| fuel].
  - destruct
      (phase1_surface_parser_goal_rank_exists
        0 (GoalExpression path (ENonterminal name)) Hglobal)
      as [rank Hrank].
    discriminate Hrank.
  - rewrite phase1_surface_expression_rank_value_at_expression_fuel.
    simpl [phase1_surface_parser_goal_rank_value].
    eapply parser_nonterminal_child_rank_decreases.
    exact Hlookup.
Qed.
'''
text = text[:start] + nonterminal + text[end:]

old_unfold = r'''  unfold phase1_surface_parser_goal_rank_value,
    phase1_surface_rank_value.
'''
new_unfold = r'''  repeat rewrite phase1_surface_parser_goal_rank_value_equation.
  unfold phase1_surface_rank_value.
'''
count = text.count(old_unfold)
if count < 6:
    raise SystemExit(f"expected at least 6 rank-value unfold sites, found {count}")
text = text.replace(old_unfold, new_unfold)

path.write_text(text)
