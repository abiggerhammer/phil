# Systems revision canonicalization production binding v1

This closes the implementation-refinement binding for already-Certified `PHIL-SYS-REV-001` after staging in PR #514.

The exact Rocq-extracted `SystemsRevisionCanonicalizationKernel.hs` is checked in at `generated/SystemsRevisionCanonicalizationKernel.hs` with SHA-256 `2d3e8443e0145fdf4d9c3a15160428d5f8a7f0422775e35a296c529f0e523b7b`. Production compiles `src/SystemsRevisionCanonicalizationKernel.hs`, which is mechanically constrained to equal that raw extraction with exactly one module-local `OPTIONS_GHC -Wno-unused-imports` pragma prepended for Rocq's unused qualified `Prelude` import.

## Production ownership

`Phil.Systems.Phase1Stage` now obtains both canonical revision construction shapes from the extracted kernel before applying the existing native encoders.

For `SystemsArtifactRevision`, production first performs the existing Phase-1 normalization. It then supplies the normalized source identity, Systems program, StageContract semantics, and lowering ledger to `planSystemsArtifactRevision`; the revision is encoded only from the coordinates returned by that plan.

For `Phase1StageContractRevision`, production supplies the ArchitectureInstance revision, realization revision, Systems revision, verifier-profile revision, source facts, dispositions, Systems mechanisms, and justifications to `planPhase1StageContractRevision`; the canonical semantic record is built only from the coordinates returned by that plan.

An impossible extracted namespace/shape mismatch terminates fail-closed rather than falling back to handwritten dependency selection.

## Explicit representation boundary

This closeout does not claim that Rocq proves the concrete representation layer. The following remain explicit ADR-019 representation/cryptographic foundations:

- normalization of concrete `SystemsArtifact`, `StageContract`, lowering-ledger, `Map`, `Set`, and list values;
- the finite mapping from returned plan coordinates to existing canonical field names;
- `SemanticForm` representation and `canonicalSemanticForm` encoding;
- the mature `systemsArtifactDigest` encoder and its concrete SHA-256 computation;
- concrete `Text`, key, revision, ordering, and container semantics; and
- collision resistance/injectivity of the concrete serializer/hash boundary.

The extracted plan owns which semantic coordinates participate. Native code realizes those coordinates into the already-established canonical representation.

## Closeout criterion

The dedicated production-binding workflow must, on one exact PR head:

1. recompile the Certified predecessors, `PHIL-SYS-REV-001`, and the implementation correspondence under Rocq 9.2;
2. fresh-extract `SystemsRevisionCanonicalizationKernel.hs`, assert SHA-256 `2d3e8443e0145fdf4d9c3a15160428d5f8a7f0422775e35a296c529f0e523b7b`, and byte-compare it with the checked-in raw kernel;
3. mechanically reconstruct and byte-compare the strict production mirror;
4. strict-typecheck the raw kernel, production mirror, and bound `Phase1Stage` path;
5. execute the unchanged 14 direct construction-plan controls against the production mirror;
6. rerun the unchanged generic Systems-stage and final StageClosure canonicalization corpora; and
7. record exact closeout identities in a dedicated artifact.

A green exact-head closeout permits `PHIL-SYS-REV-001` to move from `Discharged / Certified` to `Discharged / Implementation Refined`.
