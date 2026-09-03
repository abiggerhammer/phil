# PHIL-DATA-PRODUCT-001 — implementation refinement staging

This staging slice turns the Certified finite-product elimination semantics into a small executable kernel without changing production Haskell behavior.

## Reused refined semantics

Product mode derivation and formation uniqueness are already mechanically owned by `PHIL-DATA-MODE-001`:

- `productMode` uses the production-bound `deriveRecordMode` path; and
- `formProductBinding` uses actual `ResourceContext` consumption plus the certified aggregate-formation uniqueness gate.

This slice therefore does **not** duplicate those decisions.

## Staged executable surface

`proof/Phil/Core/DataProductImplementation.v` exposes two executable decisions:

1. product elimination admission accepts exactly when successor arity matches the ordered element contract and successor names are distinct; this is proved equivalent to Certified `ProductEliminationAccepted`; and
2. successful product restoration accepts only when the native operation actually consumed the product owner and installed the exact successor contract.

`proof/Phil/Core/DataProductImplementationExtraction.v` extracts those decisions as `DataProductKernel.hs` in CI. `app/DataProductDecisionCorrespondenceMain.hs` exercises eight direct controls including rejection precedence.

## Deliberate native boundaries

The kernel does not manufacture or reinterpret:

- concrete `ProductElementType`, `ProductValue`, `TyProduct`, `Name`, or list representation/order;
- source-to-Core product elaboration;
- actual source consumption or product binding insertion;
- the already-refined product mode or restricted-source formation checks;
- actual successor insertion through `ResourceContext`;
- concrete diagnostics and source locations.

Those facts remain native. The extracted decisions are fail-closed gates over facts established by the existing implementation.

## Staging gate

The dedicated `Phase 1 Data Product Proofs` workflow:

- compiles the existing Certified proof plus this implementation-correspondence layer under Rocq 9.2.0;
- freshly extracts `DataProductKernel.hs` and records its exact SHA-256 with the proof artifact;
- compiles and executes the eight direct extracted-kernel controls under `-Wall -Werror`; and
- reruns the unchanged seven-case DATA-015 finite-product correspondence corpus.

A green staging merge leaves `PHIL-DATA-PRODUCT-001` at `Discharged / Certified`. Exact-kernel production binding to `DataMode.eliminateProductBinding` is required before promotion to `Implementation Refined`.
