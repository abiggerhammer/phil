# PHIL-RES-LOOP-001 production binding v1

This closeout binds the already-Certified and staged Resource Loop decision surface to production without changing its semantic boundary.

## Exact kernel

The checked-in `generated/ResourceLoopKernel.hs` and `src/ResourceLoopKernel.hs` are byte-identical copies of the Rocq 9.2 extraction staged by PR #583.

Expected SHA-256:

`a9c8341d35f193300a5be18f74a3020e1211e6d19a255d31e2f09a8a43efb564`

The closeout workflow fresh-extracts the kernel and byte-compares both checked-in copies before any production-binding claim is accepted.

## Loop projection binding

`Phil.Systems.ControlStateProjection.checkStateProjection` retains ownership of concrete CFG traversal, boundary lookup, edge targeting, state-slot maps, modes, subjects, lexical-loan checks, and diagnostics.

After those native checks and the already-bound Resource Join and Resource Scope checks succeed, an actual `LoopStateBoundary` projection is also classified through `decideLoopProjectionByFacts` using concrete facts:

- the projection is an actual loop initial entry or loop backedge;
- the already-bound Resource Join decision accepts the recomputed linear ownership/subject facts;
- the projection binding domain exactly equals the declared loop-state slot domain;
- every declared slot resolves to its actual binding and satisfies the authoritative concrete slot mode and subject requirement.

The concrete Systems representation intentionally has no second copied requirement map. The final fact therefore reflects the stronger concrete condition that each bound slot is checked against the same authoritative `StateSlotContract`; no requirement is invented or independently reconstructed.

Ordinary join projections remain outside this Resource Loop gate.

## State transport binding

`Phil.Core.Value.transportValue` retains the concrete Core syntax and error policy:

- redundant explicit transport between definitionally equal types still rejects with `TransportNotRequired`;
- incompatible type families still reject with `UnsupportedTransport`;
- refined transport targets remain rejected by the existing native rule.

The Resource Loop kernel classifies the semantic transport relation underneath that syntax policy:

- the definitional-equality branch passes the actual `definitionallyEqualTy` result to the kernel and then preserves the native `TransportNotRequired` result;
- the non-definitional `TyBytes` transport branch first performs the existing explicit `dischargePropositionUsing`; only after that succeeds is `explicitEvidenceAccepted` derived from the returned nonempty `EvidenceUse` list and passed to the kernel.

No equality witness is fabricated and no unsupported transport family is widened into the Certified relation.

## Closeout evidence

The production-binding workflow requires:

1. fresh Rocq 9.2 extraction at the staged SHA;
2. byte identity of fresh, `generated/`, and `src/` kernels;
3. package-level `-Werror` build;
4. strict typechecking of the kernel and both production ownership points;
5. all 8 direct Resource Loop controls through the production kernel;
6. the unchanged 4-case RES-009/010 correspondence corpus.

A green exact-head closeout permits `PHIL-RES-LOOP-001` to move from `Discharged / Certified` to `Discharged / Implementation Refined`.
