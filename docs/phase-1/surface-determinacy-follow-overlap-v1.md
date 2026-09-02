# Phase 1 surface determinacy: FOLLOW and exact overlap completeness

This tranche continues `PHIL-SURFACE-DETERM-001` after the exact certificate binding in #565 and the nullable/FIRST fixed-point proof in #569.

`proof/Phil/Surface/GrammarDeterminacyFollowOverlap.v` computes FOLLOW facts directly over the generated `Grammar.v` tree, proves the current FOLLOW map is a fixed point, and then traverses every EBNF alternative, optional, repetition, and sequence boundary using those checked nullable/FIRST/FOLLOW facts.

The resulting overlap list is checked against `phase1_surface_determinacy_certificate` by both exact cardinality and mutual structural membership. This makes the 15-site certificate complete for the current proof-facing Grammar-v1 traversal rather than merely source-hash-bound or manually reviewed.

## Boundary

This tranche still does **not** discharge `PHIL-SURFACE-DETERM-001`.

What remains is semantic resolution of the certified overlap sites under the admitted lexical/syntactic model: reserved-keyword/identifier separation, delimiter-committed forms, relation-operator commitment, and trailing-comma/list termination. Those checked resolver lemmas must construct one admissible path/input-indexed oracle and prove that every ordinary `Phase1CompleteDerivation` is resolved by it. Only then can the proof compose with #554's `same_oracle_has_one_complete_parse` to obtain language-level unique parse.
