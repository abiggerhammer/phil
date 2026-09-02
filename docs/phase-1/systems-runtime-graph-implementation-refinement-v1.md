# Systems runtime graph implementation refinement v1

`PHIL-SYS-RUNTIME-GRAPH-001` is already Certified by PR #487. This tranche stages only its representation-neutral executable decision surface; production Haskell behavior is unchanged here. A separate exact-kernel production-binding closeout is required before the ledger may move to `Discharged / Implementation Refined`.

## Certified surface being extracted

The Certified theorem composes `PHIL-SYS-RUNTIME-001` and `PHIL-LLVM-RUNTIME-SYM-001` and establishes five structural graph facts.

### SYS-015 runtime claim/site graph

`decideRuntimeClaimGraphByFacts` owns the Certified requirement that every semantic runtime site is accepted by the selected runtime-evidence verifier. This predecessor relation already binds selected evidence, exact revision, and declared runtime cost.

Concrete claim/site domain construction, exact forward/reverse maps, source-obligation and source-fact derivation, site claiming, and physical-cost registry construction remain native finite-correspondence work.

### SYS-016 primitive/profile reuse

`decideRuntimePrimitiveReuseByFacts` owns two Certified facts:

1. site-owned contribution identity is injective, so reusing one primitive/profile cannot collapse distinct semantic sites; and
2. every physical runtime symbol is accepted by the Certified runtime-symbol identity relation, whose naming depends on physical primitive/signature identity rather than assurance metadata or claim cardinality.

Concrete profile selection, subject/site/profile maps, and runtime symbol spelling remain outside this kernel.

### SYS-018 cost attribution

`decideRuntimeCostAttributionByFacts` owns the Certified shared-charge compatibility rule: multiple contributions may share one final physical/accounting charge only when their selected cost class and cost shape agree exactly.

Concrete cost values and selected profile cost models remain explicit profile data rather than universal theorem content.

### Cumulative runtime graph

`decideSystemsRuntimeGraphByFacts` composes accepted SYS-015, SYS-016, and SYS-018 surfaces. The implementation-correspondence theorem proves that, under exact Boolean reflection hypotheses for the three groups, cumulative acceptance is equivalent to `RuntimeClaimCostGraphValid`.

## Explicit boundary

Concrete Haskell `Text`, key/revision, `Map`, `Set`, and list representation/enumeration; claim/site/subject/profile/contribution/charge graph construction; canonical stage revision serialization; exact diagnostic payloads; selected runtime evidence and profile truth; concrete numeric cost data; linker/backend/runtime behavior; and Rocq/GHC correctness remain explicit correspondence/evidence/TCB boundaries.

## Staging verification

The existing `Phase 1 Systems Runtime Graph Proofs` workflow is extended to:

- compile the Certified predecessors, theorem, and implementation-correspondence theorem under Rocq 9.2.0;
- fresh-extract `SystemsRuntimeGraphKernel.hs` with Coq `bool` mapped directly to `Prelude.Bool`;
- strict-typecheck the raw extracted kernel;
- execute **12 direct controls** spanning SYS-015, SYS-016, SYS-018, and cumulative acceptance/failure classes;
- strict-typecheck the unchanged runtime graph implementation surfaces with their already-documented warning exemption; and
- rerun the unchanged **77-case** corpus: SYS-015 (17), SYS-016 (18), and SYS-018 (42).

A green staging matrix leaves `PHIL-SYS-RUNTIME-GRAPH-001` at `Discharged / Certified`.
