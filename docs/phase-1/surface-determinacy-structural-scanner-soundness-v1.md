# Phase 1 surface determinacy: structural scanner soundness v1

This tranche continues `PHIL-SURFACE-DETERM-001` after #655 bound the seven simple resolver sites to ordinary derivations.

The remaining eight certified overlap sites use structural lookahead rather than a fixed one- or two-token prefix. `proof/Phil/Surface/GrammarDeterminacyStructuralScannerSoundness.v` factors those resolver mechanics into reusable proof-facing scanner invariants before the final derivation-soundness pass.

The proof establishes:

- maximal qualified-name tails preserve `qualified_name_remainder`, so a following `{` commits record-pattern syntax;
- a parenthesis-neutral token prefix preserves the depth/state of `parenthesis_commit_scan`, so the first top-level comma or closing `)` commits tuple versus grouped syntax;
- the same parenthesis result is reusable for parenthesized static arguments;
- brace-led static arguments commit refinement syntax on `IDENTIFIER :` and effect-set syntax on `}` or an identifier followed by a non-colon separator; and
- a relation-neutral token prefix preserves the depth/state of `relation_commit_scan`, after which a top-level relation operator or proposition boundary determines the proposition-atom decision.

The neutral-prefix scanners are deliberately separate from the ordinary EBNF derivation relation. This keeps the scanner mechanics small and opaque; the successor proof only has to show that the token prefix consumed by the relevant derived subexpression is neutral for the corresponding scanner.

This tranche does **not** yet discharge the eight structural resolver sites or `PHIL-SURFACE-DETERM-001`. The successor proof binds ordinary derivations of `pattern`, `primary_expression`, `static_argument`, and `proposition_atom` to these scanner invariants. Once those eight sites are semantically bound, the final mutual induction can show every ordinary `Phase1CompleteDerivation` follows `phase1_surface_predictive_oracle`, then compose with #554 for universal unique parsing.

Baseline: #655 merged as `685cc6951125120d1f787c1bef41717e11f94801`; branch baseline includes later non-conflicting `main` work at `42c83ba72a2eb324d135a068c38066e03e33685d`.
