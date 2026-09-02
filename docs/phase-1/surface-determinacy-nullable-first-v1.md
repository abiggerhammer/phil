# Phase 1 surface determinacy: nullable/FIRST foundation

This tranche begins the mechanized completeness bridge for `PHIL-SURFACE-DETERM-001` after #565.

`GrammarDeterminacyNullableFirst.v` computes nullable and FIRST facts directly over the exact typed grammar emitted in `Grammar.v`. It does not import nullable/FIRST tables from the Python audit. For the current Grammar-v1 tree, Rocq checks that both computations reach stable fixed points.

The overlap token type is shared with the generated determinacy certificate so the successor FOLLOW/overlap-enumeration tranche can compare its Rocq-computed local overlap inventory directly with `phase1_surface_determinacy_certificate`.

This tranche does not discharge surface determinacy. It establishes only the proof-facing nullable/FIRST foundation. FOLLOW propagation, exact overlap enumeration, resolver lemmas, admissible-oracle construction, and universal resolved-derivation coverage remain open.
