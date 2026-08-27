# Provider law implementation refinement v1

`PHIL-PROV-LAW-IMPL-001` mechanically connects the bounded PROV-007 provider-wide history-law checker to the Certified `PHIL-PROV-STATE-001` law semantics.

This first tranche is an extraction/staging slice. It does **not** yet change production Haskell acceptance.

The extracted kernel owns the exact finite traversal for:

- translating every implementation event only through the already-qualified operation/outcome correspondence;
- preserving the public operation identity while replacing only the implementation outcome with its exact public outcome;
- translating an entire implementation trace fail-closed;
- executing the resulting public trace against a deterministic finite law-state transition map; and
- rejecting a history whenever the required public-law transition is absent.

The normalized extraction model uses tuple projections for implementation events, public events, and law transition keys. The production binding tranche will project the concrete `Map` structures to canonical ascending association lists, require exact round trips, check in the byte-identical generated kernel, route `checkProviderLawTrace` acceptance through the extracted decision, and retain the handwritten traversal only for diagnostics/result reconstruction.

The theorem establishes the exact evaluator structure; it does not infer that a finite trace corpus covers every reachable runtime history. Corpus completeness, trace generation, environmental interference, backend correctness, Rocq extraction/toolchain correctness, and concrete Haskell representation correspondence remain explicit evidence or TCB boundaries.

PROV-008 lifecycle/interruption behavior remains a separate production-refinement slice after PROV-007.
