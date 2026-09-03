# Phase 1 surface determinacy: nullable/FIRST witness soundness v1

This tranche continues `PHIL-SURFACE-DETERM-001` after the predictive oracle (#582) and ordinary-derivation lookahead witnesses (#586).

`proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v` proves that the structural nullable and FIRST witnesses exposed by ordinary EBNF derivations agree with the exact Grammar-v1 nullable/FIRST fixed points computed in `GrammarDeterminacyNullableFirst.v`, under the exact grammar-wide fuel/non-nullability certificate checked in `GrammarDeterminacyPredictiveOracle.v`.

The proof is implementation-independent. It does not import Haskell parser branch order. Nonterminal cases are tied to the checked fixed-point equations, and sequence/alternative cases prove the required token-set union and fuel-definedness properties directly over the typed EBNF.

The exported bridge establishes:

- a structural nullable witness implies the computed nullable fact is true whenever the expression is covered by the checked Grammar-v1 choice-safety certificate; and
- a structural FIRST witness implies the witnessed token shape is a member of the computed FIRST set under the same certificate.

This does **not** yet discharge `PHIL-SURFACE-DETERM-001`.

The remaining global bridge is about decisions that consume nothing. It must carry accepting continuation/FOLLOW information through complete Grammar-v1 derivations, use that information to justify optional/repetition skip/stop choices, prove every ordinary `Phase1CompleteDerivation` follows `phase1_surface_predictive_oracle`, and then compose with #554 `same_oracle_has_one_complete_parse` to obtain universal unique parsing.

Baseline: #586 merged as `da188f44760fdab0ef62d79e7b90bb406bd6bc21`.
