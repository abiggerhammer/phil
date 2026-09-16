# Phase 1 surface parser correspondence — recognizer soundness

This proof slice begins the mechanized closeout of `PHIL-SURFACE-GRAMMAR-CORR-001`.

`grammar/phase1-surface.ebnf` remains the sole Phase 1 concrete-syntax authority. The existing production corpus remains valuable example-based pressure, but it does not define the accepted language and does not prove parser soundness or completeness.

The new `GrammarParserRecognizer.v` introduces a fuel-bounded executable recognizer over the already established `OracleDerives` semantics. The recognizer follows a supplied derivation oracle, consumes exact `ConcreteToken` values, constructs the corresponding structural `ParseTree`, rejects non-progressing repetition, and does not encode Haskell parser branch order.

The central theorem is:

`oracle_parse_fuel_sound`

Every successful recognizer result is an `OracleDerives` derivation for the exact grammar goal, input, remainder, and result. Instantiating the recognizer with `phase1_surface_predictive_oracle` yields:

`phase1_surface_predictive_parse_fuel_sound`

and erasure gives:

`phase1_surface_predictive_parse_fuel_ordinary_sound`.

Thus this slice establishes the soundness half of an implementation-independent executable Grammar-v1 reference parser: the reference recognizer cannot accept a token stream that the normative grammar does not derive.

This slice does **not** yet discharge `PHIL-SURFACE-GRAMMAR-CORR-001`. Remaining work is:

1. prove recognizer completeness for oracle-resolved derivations under a sufficient fuel bound;
2. derive a Grammar-v1 complete-input fuel bound from the finite grammar plus token-stream progress;
3. establish the exact production lexer-token to `ConcreteToken` correspondence while retaining Unicode/source decoding as an explicit front-end representation boundary where appropriate;
4. mechanically bind production parser acceptance to the verified reference parser in both directions, so neither Haskell success outside Grammar v1 nor Haskell rejection of a Grammar-v1 member can define the language;
5. retain whole-file consumption and the portable positive/negative corpus as regression evidence around that universal correspondence.

The already-discharged `PHIL-SURFACE-DETERM-001` supplies unique grammar interpretation once a complete Grammar-v1 derivation exists; it is complementary to, not a substitute for, this parser/language correspondence proof.
