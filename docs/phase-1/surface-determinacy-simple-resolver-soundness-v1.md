# Phase 1 surface determinacy: simple resolver soundness v1

This slice continues the final `PHIL-SURFACE-DETERM-001` tranche after #651.

`proof/Phil/Surface/GrammarDeterminacySimpleResolverSoundness.v` connects the seven simple certified resolver sites to ordinary Grammar-v1 derivations.

For the two reserved-prefix overlap families it proves semantic, not example-only, commitments:

- any ordinary derivation of `provider_contract_decl` begins with `provider` followed by an `IDENTIFIER`, so `provider_declaration_decision` selects declaration branch 6;
- any ordinary derivation of `provider_implementation_decl` begins with `provider implementation`, so the same resolver selects branch 7;
- the `generic_requirement` branch-4 and branch-8 expressions are tied to the exact generated grammar table and arbitrary derivations of those forms commit the resolver to branches 4 and 8 respectively.

For the five trailing-comma repetition sites, the proof generalizes the previously checked concrete examples to arbitrary tails: comma-plus-identifier continues, close stops, and comma-plus-close stops. The accepting-continuation facts needed to show which stop form occurs at an ordinary repetition boundary were proved in #651 and are consumed by the final assembly theorem.

The file also exports small derivation inversion and path-suffix lemmas used by the remaining structural resolver and oracle-assembly proofs.

This slice does **not** yet discharge `PHIL-SURFACE-DETERM-001`. The remaining resolver work is the eight structural scanner sites; after those are semantically bound, the final mutual induction can show every ordinary `Phase1CompleteDerivation` follows `phase1_surface_predictive_oracle` and compose with #554 for universal unique parsing.

Baseline: #651 merged as `578637323e4a32fbd73ca826e2570f73c30d734a`.
