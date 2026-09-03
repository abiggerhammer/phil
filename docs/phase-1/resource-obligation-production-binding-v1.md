# PHIL-RES-OBL-001 — production binding closeout

This closeout binds the exact Resource Obligation decision kernel staged by #590 to the production `joinBranches` normalization path.

## Exact kernel

The staged `ResourceObligationKernel.hs` has SHA-256:

`ad29db6a9cd16549ca39b97150b80383a6efc520d1f9e235a29ed869cd901345`

The production closeout checks that fresh Rocq 9.2 extraction, `generated/ResourceObligationKernel.hs`, and `src/ResourceObligationKernel.hs` are byte-identical.

## Production ownership point

`Phil.Core.Process.joinBranches` remains the owner of continuing-path reconvergence. It still computes the joined `ResourceContext` and still normalizes each continuing path by replacing only that resource context.

The bound kernel is an independent fail-closed check around that actual normalization result. For each continuing path, production computes the union of obligation IDs visible in the before and after `residualObligations` maps and calls:

`decidePendingObligationReconvergenceByFacts pendingBefore pendingAfter`

with both Boolean facts derived from real map membership. A pending input obligation must still be present after normalization. A non-pending input imposes no new disposition claim, exactly matching the Certified theorem.

Terminal paths are not treated as reconvergence inputs and remain outside this gate.

## Boundaries

This kernel does not decide whether an obligation is validly discharged, runtime-bound, assumed, or exported. Those remain explicit semantic events owned by their existing boundary/evidence rules. The theorem needs no synthetic disposition Boolean: if an obligation remains pending, the Certified proof already derives that reconvergence itself did not fabricate any explicit disposition.

The kernel also does not replace `ProcessJoin.v`, resource-context joining, obligation creation/discharge logic, or concrete `Map` representation correctness.

## Closeout gate

`Phase 1 Resource Obligation Production Binding` requires:

1. fresh Rocq 9.2 extraction at the staged kernel SHA;
2. byte identity of fresh, generated, and production kernels;
3. package-level `-Werror` build;
4. strict typechecking of the production Process binding and direct harness;
5. all four Boolean truth-table controls through the production kernel;
6. the unchanged two-case RES-011 reconvergence corpus.

A fully green exact head permits `PHIL-RES-OBL-001` to move from `Discharged / Certified` to `Discharged / Implementation Refined`.
