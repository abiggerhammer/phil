# Phase 1 surface determinacy — ordinary derivation lookahead bridge

This proof slice continues `PHIL-SURFACE-DETERM-001` after the exact predictive oracle landed in #582.

`proof/Phil/Surface/GrammarDerivationLookahead.v` proves implementation-independent semantic facts about the ordinary Grammar-v1 derivation relation:

- every ordinary expression/sequence/repetition derivation consumes a prefix of its input;
- an ordinary expression derivation that consumes no token has a structural nullable witness;
- an ordinary consuming expression derivation has a structural FIRST witness for the shape of its first concrete token; and
- the sequence/repetition cases preserve those witnesses through nullable prefixes and repeated bodies.

The witnesses are intentionally relational rather than imported from the Python audit or Haskell parser. They are the semantic side of the bridge to the checked nullable/FIRST fixed points from #569.

## Scope

This slice does not discharge `PHIL-SURFACE-DETERM-001`.

Successor work proves that every structural nullable/FIRST witness is represented by the #569 fixed-point facts, then carries an accepting continuation/FOLLOW invariant through a complete derivation. Those lemmas are what let the #582 predictive oracle's ordinary stop/skip choices be justified rather than merely computed. The final composition remains:

1. every ordinary `Phase1CompleteDerivation` resolves under the single `phase1_surface_predictive_oracle`; and
2. #554 `same_oracle_has_one_complete_parse` yields universal unique parsing for exact Grammar-v1.

Baseline: #582 merged as `e6fd5c3a999eb00abed0df637501722925584786`.
