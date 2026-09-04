from pathlib import Path


script30 = Path("scripts/debug_phase1_surface_witness_soundness_30.py").read_text()
exec(compile(script30, "<debug30>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()

lookup_marker = "Lemma phase1_surface_first_lookup_mem :"
next_marker = "Lemma first_witness_nonterminal_sem_case :"
lookup_start = source.index(lookup_marker)
lookup_start = source.rfind("\n", 0, lookup_start) + 1
next_start = source.index(next_marker, lookup_start)
next_start = source.rfind("\n", 0, next_start) + 1

new_lookup = r'''Lemma first_expression_fuel_result_eq :
  forall nullable_facts first_facts expression tokens,
    first_expression_fuel
      expression_fuel nullable_facts first_facts expression = Some tokens ->
    first_expression nullable_facts first_facts expression = tokens.
Proof.
  intros nullable_facts first_facts expression tokens Hfirst.
  unfold first_expression.
  rewrite Hfirst.
  reflexivity.
Qed.

Lemma token_mem_eq_transport :
  forall token left right,
    left = right ->
    token_mem token right = true ->
    token_mem token left = true.
Proof.
  intros token left right Heq Hmem.
  rewrite Heq.
  exact Hmem.
Qed.

Lemma phase1_surface_first_lookup_mem :
  forall token name body tokens,
    lookupRule name phase1_surface_rules = Some body ->
    first_expression_fuel
      expression_fuel
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      body = Some tokens ->
    token_mem token tokens = true ->
    token_mem token
      (lookup_tokens name phase1_surface_first_facts) = true.
Proof.
  intros token name body tokens Hlookup Hbody_first Hmem.
  eapply token_mem_eq_transport.
  - eapply eq_trans.
    + exact (phase1_surface_first_lookup_rule name body Hlookup).
    + exact
        (first_expression_fuel_result_eq
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          body tokens Hbody_first).
  - exact Hmem.
Qed.

'''

source = source[:lookup_start] + new_lookup + source[next_start:]
path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
