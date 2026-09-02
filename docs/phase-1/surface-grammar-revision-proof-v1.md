# Phase 1 grammar revision binding proof

Ledger obligation: `PHIL-SURFACE-REV-001`
Matrix case: `SURF-006`

This proof closes the Phase-1 concrete-grammar revision rule without inventing a long-term migration policy.

## Certified rule

A portable SourceBundle is checked against one explicitly selected concrete-grammar revision. In Phase 1:

- exactly one well-formed grammar revision must be present;
- the bundle revision must equal the selected front-end revision exactly;
- missing, duplicate, malformed, and incompatible revisions reject before source lineage is resolved;
- successful binding retains the selected revision exactly;
- changing the selected grammar revision reopens an old bundle rather than silently reinterpreting it;
- source payload/trivia changes cannot themselves rewrite the grammar revision carried by the bundle; and
- if a future system admits cross-revision compatibility, that admission must flow through an explicit compatibility/migration relation rather than the Phase-1 exact-equality rule.

The Rocq proof imports the typed `Grammar.v` artifact generated deterministically from `grammar/phase1-surface.ebnf`. Its `canonicalPhase1GrammarRevision` is exactly `"sha256:" ++ phase1_surface_grammar_source_sha256`.

## Production correspondence

`Phil.Surface.Lineage.decodePortableSourceBundleForGrammar` implements the same exact-equality gate. The dedicated correspondence job independently hashes `grammar/phase1-surface.ebnf` and reruns `Phase1GrammarRevisionBindingMain.hs`, which requires the resulting SHA-256 to equal the Haskell `canonicalGrammarRevisionV1` and pressure-tests exact acceptance plus missing, duplicate, malformed, and incompatible rejection.

The broader portable-lineage corpus is rerun unchanged as well.

## Explicit boundaries

This theorem does not prove SHA-256 collision resistance, the correctness of the Python EBNF parser/renderer, Haskell `Text` decoding/equality, parser/grammar soundness and completeness, or cross-revision semantic compatibility. Those remain explicit cryptographic/tooling/correspondence boundaries or separate obligations.

No migration relation exists in Phase 1. A future migration or compatibility mechanism must therefore add a new explicit semantic relation and proof obligation rather than weakening this exact binding in place.
