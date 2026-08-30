# Phase 1 Systems stage-closure proof v1

This slice certifies `PHIL-SYS-STAGE-CLOSURE-001`, the generalized StageContract closure obligation implemented by the coarse SYS-002/003 envelope and the final SYS-020 closure layer.

## Source responsibilities close exactly once

The normalized proof treats every live source fact, edge, or obligation crossing into Systems as a `SourceResponsibility`. A successful closure has an exact responsibility/disposition domain: every live responsibility has one disposition entry and no non-live responsibility is invented.

Permitted dispositions are the Phase-1 forms already used by the implementation:

- realized by target mechanisms;
- preserved by target mechanisms;
- explicitly exported to a named next-stage requirement; or
- assumption-dependent, with a nonempty exact assumption identity around another permitted disposition.

Any target mechanism cited by a realized/preserved disposition must exist in the exact target-mechanism domain.

For source facts, the generalized responsibility map is explicitly projected onto the already Certified `PHIL-SYS-FACT-001` model. A live source fact therefore inherits that certificate's exact fact coverage and disposition validity rather than receiving a second independent fact semantics.

## Target mechanisms require reverse justification

Every semantically significant target mechanism is assigned one explicit kind: operation, runtime site, ownership transfer, carrier, or cost mechanism. Exact target coverage requires every live mechanism to have both a kind and a justification.

A justification may be grounded by one or more exact live source responsibilities, an explicit realization reason, an exact provider/qualification reason, or an explicit derived-obligation reason. An assumption by itself is not a target-mechanism justification. Source references inside a target justification must name live source responsibilities exactly.

Concrete enumeration of target operations/sites/transfers/carriers/cost mechanisms remains an implementation-correspondence boundary; the theorem certifies the bidirectional accounting relation after that enumeration.

## Final SYS-020 closure binds one common StageContract lineage

The final identity relation requires the concrete correspondence trunk and the evidence/realization/runtime/cost/next-stage trunk to agree exactly on:

- SubjectStage revision;
- ArchitectureInstance revision;
- ArchitectureRealization revision;
- SystemsArtifact revision;
- coarse Phase-1 StageContract revision; and
- verifier-profile revision.

The stored final Systems revision must equal the recomputed revision from the common artifact, and the stored closed StageContract revision must equal the recomputed final revision. Cross-witness trunk mixing, stale stored Systems identity, and stale final StageContract identity therefore reject.

## Validity scope remains exact

The aggregate closure composes Certified `PHIL-ASSURE-VALIDITY-001`. If target or compilation-profile dimensions are bound by the selected validity scope, changing either bound dimension prevents reuse of the closed-stage authority. The proof does not treat final closure as permission to transplant evidence across a changed target/profile.

## Correspondence evidence

The dedicated workflow re-runs the unchanged implementation corpus:

- `test/Phase1GenericSystemsStageMain.hs` — 16 SYS-001/002/003 generic StageContract cases, including missing source dispositions, missing/unjustified target mechanisms, unknown source/mechanism references, empty assumption dependencies, and deterministic reconstruction;
- `test/Phase1StageClosureMain.hs` — 20 SYS-020 cases covering upload/Steve closure, exact trunk agreement, recomputed Systems identity, semantic/nonsemantic revision sensitivity, stale stored identities, cross-witness trunk rejection, and deterministic final reconstruction.

Total unchanged correspondence corpus: **36 cases**.

## Explicit residual boundary

This certificate does not mechanize:

- concrete Haskell `Text`, `Map`, `Set`, or list enumeration and equality;
- concrete extraction of source facts/edges/obligations into the normalized responsibility domain;
- concrete enumeration of semantically significant operations, runtime sites, ownership transfers, carriers, and cost mechanisms;
- canonical `SemanticForm` serialization or digest collision resistance;
- witness-specific choice of the applicable terminal concrete trunk;
- exact diagnostics;
- Haskell implementation equivalence; or
- Rocq kernel/toolchain correctness.

Those remain explicit implementation-correspondence or TCB boundaries.

Baseline at proof-branch cut: `9f59416f8f3dfa800941ab77f8a62f1b3a7d5e55` (#439 merge).