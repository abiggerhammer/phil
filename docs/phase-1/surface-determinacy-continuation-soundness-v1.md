# Phase 1 surface determinacy: accepting continuation/FOLLOW soundness v1

This tranche continues `PHIL-SURFACE-DETERM-001` after the nullable/FIRST witness bridge in #592.

`proof/Phil/Surface/GrammarDeterminacyContinuationSoundness.v` proves the accepting-continuation facts needed by the final ordinary-derivation -> predictive-oracle theorem. It mirrors the same local FOLLOW propagation already checked in `GrammarDeterminacyFollowOverlap.v`:

- the continuation of a sequence item is `FIRST(suffix)`, extended with the outer continuation when the suffix is nullable; and
- the continuation of a repetition body is `FIRST(body) ∪ outer_follow`.

The proof connects ordinary `DerivesSequence` and `DerivesRepetition` evidence to those computed continuation sets. A consuming derivation is justified by the structural FIRST witness from #586 and its computed-table soundness from #592. A zero-consuming derivation inherits the accepting outer continuation, with nullable sequence evidence likewise discharged through #592.

The tranche also records the exact current Grammar-v1 continuation-overlap surface:

- there are **zero** `OptionalFollowOverlap` sites; and
- there are exactly **five** `RepeatFollowOverlap` sites, all five belonging to the already-certified trailing-comma resolver family.

A generic disjointness lemma shows that an accepting continuation token cannot start a non-nullable body when the body's computed FIRST set has empty intersection with the outer continuation. This is the resolver-independent fact used at non-overlap optional/repetition sites.

This does **not** yet discharge `PHIL-SURFACE-DETERM-001`.

The remaining theorem is now the final structural bridge: prove that every ordinary `Phase1CompleteDerivation` is an `OracleResolvedPhase1CompleteDerivation phase1_surface_predictive_oracle`. Non-overlap choices use nullable/FIRST plus the continuation lemmas here; the exact reviewed overlap sites use the certified resolver. Composing that theorem with #554 `same_oracle_has_one_complete_parse` yields universal unique parsing for Grammar-v1.

Baseline: #592 merged as `4f7a4d80f8f9e7bfe083d6d1adcf187612269b1e`.
