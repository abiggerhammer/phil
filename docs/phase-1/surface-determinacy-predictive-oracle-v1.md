# Phase 1 Grammar-v1 predictive oracle

This tranche constructs the single proof-facing decision oracle needed for the final `PHIL-SURFACE-DETERM-001` uniqueness bridge.

The oracle is implementation-independent. It reconstructs the exact generated `EbnfExpression` at a `SyntaxPath` starting from `source_file`; at the 15 machine-derived overlap sites it gives precedence to the checked resolver assembled by the #575/#576 resolver tranches; at all other alternative, optional, and repetition choice points it uses the mechanized nullable/FIRST facts from #569.

The tranche also checks, over every exact Grammar-v1 rule body, that alternative branches, optional bodies, and repetition bodies are non-nullable. This removes hidden epsilon-choice policy from the predictive fallback and leaves the next proof with a purely structural obligation.

This does **not** by itself discharge `PHIL-SURFACE-DETERM-001`. The remaining theorem must prove that every ordinary `Phase1CompleteDerivation` is an `OracleResolvedPhase1CompleteDerivation` for this exact oracle. Once that is established, #554's `same_oracle_has_one_complete_parse` gives universal unique parsing immediately.
