from pathlib import Path

path = Path("proof/Phil/Surface/GrammarParserTotalFuelValue.v")
text = path.read_text()

old = r'''  - unfold phase1_surface_parser_goal_rank_value,
      phase1_surface_rank_value,
      phase1_surface_parser_goal_rank_fuel.
    simpl.
    change
      (parser_expression_rank phase1_surface_parser_rank_facts body <
       S (parser_rank_lookup name phase1_surface_parser_rank_facts)).
    eapply parser_nonterminal_child_rank_decreases.
    exact Hlookup.
'''

new = r'''  - change
      (parser_expression_rank phase1_surface_parser_rank_facts body <
       S (parser_rank_lookup name phase1_surface_parser_rank_facts)).
    eapply parser_nonterminal_child_rank_decreases.
    exact Hlookup.
'''

if old not in text:
    raise SystemExit(f"nonterminal value-rank proof shape not found in {path}")

path.write_text(text.replace(old, new, 1))
