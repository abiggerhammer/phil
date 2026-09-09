from pathlib import Path
import runpy

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

# Rewrite the rank-value representation itself so expression goals inspect the
# outer syntax constructor before consulting the fuelled evaluator.  This keeps
# the exact same numeric rank when the evaluator succeeds, but prevents Rocq's
# conversion checker from unfolding the concrete 256-fuel Grammar-v1 rank
# computation merely to reduce a nonterminal goal.
runpy.run_path("scripts/patch_total_fuel_value_shallow_rank.py", run_name="__main__")
