# Phase 1 surface determinacy — structural resolver tranche

This tranche continues `PHIL-SURFACE-DETERM-001` after #575.

## What is checked here

`proof/Phil/Surface/GrammarDeterminacyStructuralResolvers.v` binds the remaining eight machine-derived Grammar-v1 overlap sites to four path/input-indexed resolver families:

- maximal qualified-name commitment for ordinary identifier patterns versus record patterns;
- balanced parenthesis scanning, where a top-level comma commits tuple syntax and the matching close commits grouping/static-value syntax;
- brace commitment for static arguments, where `:` after the initial identifier commits refinement type syntax and the effect-set forms take the other certified branch; and
- proposition-atom relation commitment, where an explicit top-level relation operator after the complete left additive operand commits `relation_proposition`, otherwise the literal/grouped/claim-application branch is selected.

The proof also checks that these eight sites are disjoint from the seven resolver sites proved by #575 and that the two resolver tranches together cover all 15 entries in the exact generated overlap certificate.

The combined `phase1_surface_certified_overlap_resolver` remains independent of Haskell parser alternative order.

## What this does not prove

This tranche does not yet discharge `PHIL-SURFACE-DETERM-001`.

The remaining bridge is global rather than site-inventory work: extend the admissible oracle across non-overlap choice points and prove that every ordinary complete Grammar-v1 derivation is oracle-resolved by that one path/input-indexed oracle. That theorem can then compose with #554's `same_oracle_has_one_complete_parse` to establish universal unique parsing for the exact generated grammar.

Source-byte/lexer correspondence remains separately bounded by `PHIL-SURFACE-GRAMMAR-CORR-001`.
