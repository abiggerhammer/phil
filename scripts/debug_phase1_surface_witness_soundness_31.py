from pathlib import Path


script30 = Path("scripts/debug_phase1_surface_witness_soundness_30.py").read_text()
exec(compile(script30, "<debug30>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()

old_lookup = r'''Lemma phase1_surface_first_lookup_mem :
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
            pose proof
              (phase1_surface_first_lookup_rule name body Hlookup)
              as Hlookup_fact.
            unfold first_expression in Hlookup_fact.
            rewrite Hbody_first in Hlookup_fact.
            simpl in Hlookup_fact.
            rewrite Hlookup_fact.
            exact Hmem.
          Qed.
'''

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

if old_lookup not in source:
    raise SystemExit("Debug 31 lookup block did not match semantic transform output")
source = source.replace(old_lookup, new_lookup, 1)

path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
