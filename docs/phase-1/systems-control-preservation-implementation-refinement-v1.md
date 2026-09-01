# Systems Control Preservation Implementation Refinement v1

`PHIL-SYS-CONTROL-001` is already Certified. This tranche stages only its representation-neutral executable decision surface; production behavior remains unchanged.

## Extracted semantic decisions

`SystemsControlPreservationImplementation.v` reflects the cumulative SYS-007--010 theorem family into five ordered decision kernels.

### SYS-007 branch resource/failure preservation

`decideBranchPreservationByFacts` admits a branch site only when the semantic outcome domain is exact, every tracked owner's fate domain is exact, every owner fate is realized exactly once, terminal/fatal control classification is preserved, and every tracked value is an owning value.

The extracted kernel deliberately does not enumerate CFG arms, values, releases, or cleanup operations. Native Haskell continues to construct those facts and retain the exact diagnostic payloads.

### SYS-008 control-state and closure-capture projection

`decideStateProjectionByFacts` requires exact projection kind and slot domain, exact restricted-owner modes and fixed subjects, unique restricted ownership, complete linear-owner coverage, no scoped-loan escape, exactly one carrier for each restricted capture, and no sharing of a restricted capture carrier.

This is the normalized semantic decision behind join/backedge state projection and exactly-once closure capture. Boundary grouping, predecessor counting, Map/Set construction, subject lookup, and carrier enumeration remain native correspondence work.

### SYS-009 protocol state correspondence

`decideProtocolPreservationByFacts` requires checked semantic correspondence rather than runtime transport coincidence, an exact target site and exact transport use, exact outcome domain, exact protocol instance and role, a fresh successor, exactly-once predecessor consumption and successor production, and acyclic endpoint lineage.

Concrete endpoint/transition lookup, operation/terminator decoding, transport-role inspection, target-site uniqueness, and lineage graph construction remain native representation boundaries.

### SYS-010 boundary commit correspondence

`decideBoundaryCommitByFacts` requires an exact source runtime fact, transport, owner, semantic subject, length relation, runtime site kind, runtime revision/evidence, protocol transition, successful successor-producing commit, terminal failure behavior, and completeness before success.

The kernel intentionally starts after source-fact lookup, concrete Systems value/subject lookup, exact boundary-operation decoding, and runtime/protocol evidence construction.

### Cumulative stage

`decideSystemsControlByFacts` composes successful SYS-007, SYS-008, SYS-009, and SYS-010 decisions in predecessor order. The Rocq correspondence theorem makes each predecessor acceptance an explicit premise rather than hiding cumulative success in a native representation choice.

## Representation and competence boundary

The staging kernel deliberately begins after concrete representation work. These remain explicit Haskell/correspondence boundaries:

- canonical stage-revision construction and `SemanticForm` serialization;
- concrete `Text`, key, revision, `Map`, `Set`, list, CFG, block, operation, and value equality/enumeration;
- branch-arm, release/cleanup, predecessor/backedge, closure-carrier, endpoint/transition, and lineage-graph construction;
- exact source-subject, owner, protocol, runtime-site, revision, evidence, and target-site lookup;
- correspondence between native aggregate facts and each kernel Boolean input;
- exact diagnostic payload construction and traversal/failure precedence beyond the normalized semantic gate order;
- truth/completeness of source facts, protocol correspondence, runtime evidence, realization evidence, and external assumptions; and
- Rocq extraction/toolchain and Haskell runtime correctness.

Production `BranchResourceFailure.hs`, `ControlStateProjection.hs`, `ProtocolStateCorrespondence.hs`, and `BoundaryCommitCorrespondence.hs` are unchanged in this staging PR. A separate closeout must check in the exact extracted kernel and bind the native semantic acceptance paths before the ledger can move from `Discharged / Certified` to `Discharged / Implementation Refined`.

## Staging verification

The existing `Phase 1 Systems Control Preservation Proofs` workflow is extended to:

- compile the Certified proof plus implementation-correspondence proof;
- fresh-extract `SystemsControlPreservationKernel.hs` under Rocq 9.2;
- strict-typecheck and execute 44 direct decision controls;
- strict-typecheck the unchanged SYS-007--010 production chain and tests;
- rerun the unchanged cumulative 46-case SYS-007--010 corpus; and
- record proof, extraction, production, test, harness, and staging-document identities.
