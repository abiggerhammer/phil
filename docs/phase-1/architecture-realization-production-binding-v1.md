# Architecture realization production binding v1

This closeout binds the architecture-owned realization construction semantics from Certified `PHIL-ARCH-REALIZE-001` to production while composing with the independently production-refined provider-replacement semantics from `PHIL-PROV-REPLACE-001`.

## Certified construction plan

PR #402 staged `planArchitectureRealization`, whose three coordinates are exactly:

1. the selected architecture `InstanceKey`;
2. the exact `InstanceRevision`; and
3. the selected realization semantics.

The fresh Rocq extraction is checked in byte-for-byte as `generated/ArchitectureRealizationKernel.hs`, with SHA-256:

`d619e0155565e2337a49d47c10e54653a3d171f79e9ef7773163065f75dee6ae`

Because the extractor emits an unused qualified `Prelude` import, production uses `src/ArchitectureRealizationKernel.hs`, which is mechanically the single compiler pragma

`{-# OPTIONS_GHC -Wno-unused-imports #-}`

followed by the exact raw extraction. The dedicated workflow constructs that expected mirror and byte-compares it before strict compilation. No semantic code is added to the mirror.

## Production binding

`deriveArchitectureRealizationIdentity` now passes the exact instance key, exact instance revision, and selected realization semantics to the extracted plan and serializes only the returned plan coordinates using the unchanged native `phil.realization.canonical.v1:` encoding.

The plan has one constructor and no rejection case, so production does not invent a synthetic namespace or fail-closed branch that is absent from the Certified model.

The native representation boundary remains explicit: `SemanticForm` canonicalization, `Text` encoding, record-field spelling, and collision-freedom of the concrete revision representation remain Haskell/runtime foundations rather than Rocq claims.

## Provider replacement composition

PR #409 separately production-bound Certified `PHIL-PROV-REPLACE-001` to its exact extracted decision kernel. This closeout therefore does not duplicate replacement checking. The unchanged ARCH-010 corpus composes:

- stable abstract architecture instance identity;
- changed realization construction;
- independently checked provider replacement;
- fresh qualification/evidence/admission lineage; and
- explicitly scoped evidence reuse.

## Exact-head verification

The production-binding workflow:

- rebuilds the Certified ARCH-ID / ARCH-INST / PROV-REPLACE / ARCH-REALIZE chain and realization-construction correspondence;
- fresh-extracts and byte-compares the raw `d619e015…` kernel;
- verifies the raw-to-production-mirror byte relation;
- strict-compiles the mirror and strict-builds the composed production library;
- reruns the six unchanged direct construction-plan controls;
- reruns the twelve unchanged ARCH-010 provider-replacement cases; and
- records exact raw kernel, production mirror, provider-replacement kernel/checker, `Static.hs`, Cabal, harness, corpus, and documentation identities.

`cabal check` is deliberately outside this implementation-correspondence workflow; unrelated Hackage publication metadata is not part of this obligation.

If the exact-head matrix is green, `PHIL-ARCH-REALIZE-001` can move to `Discharged / Implementation Refined`.
