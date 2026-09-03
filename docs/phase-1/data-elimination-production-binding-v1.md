# PHIL-DATA-ELIM-001 — production binding closeout

This closeout binds the exact `DataEliminationKernel.hs` staged by #605 to the production Data Elimination ownership points while preserving concrete names, `ResourceContext` state, lexical-scope elaboration, and diagnostics in native Haskell.

## Exact staged kernel

- staging PR: #605
- exact green staging head: `ec6a248b1d74a8787d8cf549ef89ef4cafdf62d9`
- staging merge: `88e8c4747240d9d485bfe326234a112145263b6d`
- Phase 1 Data Elimination Proofs run: `33720304571`
- staging artifact: `9880001729`
- staging artifact digest: `sha256:5e401a37259441d0cb40f87488acb5f594cd4b0e065ab3609b4e4ea0ab1bf91d`
- exact kernel SHA-256: `e03de46fdb1791bd6f3ee96cd9acdd6065b0b55d4d717597f86c86fbd1df3ddd`

`generated/DataEliminationKernel.hs` and `src/DataEliminationKernel.hs` are byte-identical copies of that extraction. The closeout workflow freshly extracts the kernel under Rocq 9.2.0 and refuses byte drift.

## Production ownership points

`Phil.Core.DataEliminationKernelBridge` is the only representation bridge from concrete `Phil.Core.Syntax.Mode` plus native disposition categories to the extracted kernel types.

`Phil.Core.DataDestruction` keeps native field names, `Map` construction, unknown-field detection, duplicate-disposition diagnostics, and `ResourceContext` errors. It now:

1. compares every native field-disposition result with the Certified kernel decision before accepting the plan;
2. requires the Certified plan decision after the native map has proved disposition-key distinctness and every native field check has succeeded;
3. exposes the Phase-1 aggregate-disposition boundary explicitly, preserving the native `ImplicitPartialRemainderRejected` error while requiring kernel agreement;
4. centralizes the existing consuming aggregate pattern in `consumeAggregateFields`: the real `ResourceContext.useBinding` consumes the restricted aggregate, real `insertBinding` calls restore explicitly bound fields, duplicate/freshness errors remain native, and only then are exact aggregate-consumed / successor-exact / successor-distinct facts supplied to the kernel.

No hidden remainder or successor ownership is manufactured by the kernel.

`Phil.Core.DataBorrow` retains native field lookup and the real `startSharedLoan` / `endSharedLoan` operations. After a declared field and real loan start succeed, it derives the five Certified lifecycle facts from the actual immutable context:

1. field lookup succeeded;
2. the exact owner is in the real shared-loan set;
3. `useBinding` on the owner is blocked as `OwnerBorrowed`;
4. `ensureComplete` rejects the active owner loan at the lexical boundary; and
5. a pure evaluation of the real `endSharedLoan` returns the exact pre-loan context.

The extracted borrow-lifecycle decision must accept those facts before the borrowed view is returned. Native errors remain authoritative for concrete payloads and ordering.

## Closeout gate

`Phase 1 Data Elimination Production Binding` requires:

- fresh Rocq 9.2 extraction and SHA-256 verification against the #605 staged kernel;
- byte identity of fresh, generated, and production kernel copies;
- the ordinary package-library `-Werror` build as a broad regression gate;
- strict `-Wall -Werror` typechecking under the Cabal environment of the exact kernel, bridge, `DataDestruction`, `DataBorrow`, direct extracted-kernel harness, and production-binding harness;
- all 23 direct kernel controls through `src/DataEliminationKernel.hs`;
- production-path controls covering disposition legality, native diagnostic preservation, aggregate remainder policy, consuming transfer, duplicate successor rejection, and scoped borrow lifecycle; and
- the unchanged DATA-004/005/006/016 record/sum/borrow/affine-omission correspondence corpus.

The Phase-1 semantic modules are currently strict-typechecked under the Cabal environment rather than listed as Cabal library modules; this closeout preserves that repository convention rather than introducing an unrelated packaging change.

A fully green exact head closes machine implementation refinement for `PHIL-DATA-ELIM-001`.
