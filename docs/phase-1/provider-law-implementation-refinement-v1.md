# Provider law implementation refinement v1

`PHIL-PROV-LAW-IMPL-001` mechanically connects the bounded PROV-007 provider-wide history-law checker to the Certified `PHIL-PROV-STATE-001` law semantics.

The first tranche established and extracted the executable finite evaluator. This production-binding tranche makes that extracted evaluator the owner of production `checkProviderLawTrace` acceptance.

The extracted kernel owns the exact finite traversal for:

- translating every implementation event only through the already-qualified operation/outcome correspondence;
- preserving the public operation identity while replacing only the implementation outcome with its exact public outcome;
- translating an entire implementation trace fail-closed;
- executing the resulting public trace against a deterministic finite law-state transition map; and
- rejecting a history whenever the required public-law transition is absent.

Production binding projects the concrete checked-operation correspondence maps and law-transition map into canonical ascending association lists, projects implementation events into the normalized tuple representation, and requires every provider-owned `Map` involved in the projection to round-trip canonically before invoking the kernel. The checked-in `ProviderLawQualificationKernel.hs` must remain byte-identical to fresh Rocq extraction.

`checkProviderLawTrace` now treats the extracted Boolean decision as authoritative. The prior handwritten traversal remains only to reconstruct the public trace, final law state, and detailed diagnostic error. Acceptance/reconstruction disagreement in either direction fails closed with `ProviderLawQualificationRepresentationMismatch`.

The theorem and production binding establish the exact evaluator structure and its concrete Haskell correspondence; they do not infer that a finite trace corpus covers every reachable runtime history. Corpus completeness, trace generation, environmental interference, backend correctness, Rocq extraction/toolchain correctness, and the remaining compiler/runtime TCB stay explicit evidence or trust boundaries.

Once the exact-head extraction/typecheck workflow and ordinary regression matrix are green, `PHIL-PROV-LAW-IMPL-001` is Implementation Refined. PROV-008 lifecycle/interruption behavior remains a separate production-refinement slice after PROV-007.
