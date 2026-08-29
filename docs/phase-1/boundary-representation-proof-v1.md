# Phase 1 boundary representation proof v1

`PHIL-BND-REP-001` certifies the bounded BND-004–007 representation-correspondence and direction layer.

The Rocq model in `proof/Phil/Core/BoundaryRepresentation.v` mirrors the production checker boundary without claiming concrete Haskell representation equivalence. It proves that successful mapping is gated by exact representation identity, grammar identity, semantic value-type revision, recognized grammar, and recognized source value. The resulting correspondence evidence records exactly the admitted representation/grammar/type, the recognized grammar value, and the explicitly requested semantic value.

The model also proves the ordered fail-closed mismatch gates, distinguishes a competent mapping rejection from recognition failure, preserves the recognized source identity across transforming mappings, keeps distinct source/semantic target identities distinct when the mapping is transforming, and enforces receive-only/send-only/bidirectional use exactly.

This proof does **not** establish the truth of a user- or provider-supplied semantic correspondence. Such truth/competence remains separately admitted evidence. It also does not certify encoding, serialization, ABI/layout, zero-copy realization, or typed protocol progression; those remain separate boundary obligations.

## Correspondence gate

The dedicated workflow typechecks the unchanged production paths and reruns the unchanged BND-004–007 corpus:

- `Phase1BoundaryMappingMain.hs` — 4 cases;
- `Phase1BoundaryMappingFailureMain.hs` — 2 cases;
- `Phase1TransformingBoundaryMappingMain.hs` — 2 cases;
- `Phase1BoundaryDirectionMain.hs` — 5 cases.

Total: **13 unchanged cases**.

## Residual trust boundary

Rocq kernel/toolchain correctness remains trusted. Concrete Haskell `Text`, `Name`, `GrammarId`, `BoundaryRepresentationId`, and `ValueTypeRevision` equality; exact error reconstruction/order; the competence/truth of explicit mapping dispositions; parser/recognizer correspondence; and Haskell implementation equivalence remain explicit boundaries.
