# Systems runtime graph implementation refinement v1

`PHIL-SYS-RUNTIME-GRAPH-001` is already Certified by PR #487. This tranche stages only its representation-neutral executable decision surface; production Haskell behavior is unchanged here. A separate exact-kernel production-binding closeout is required before the ledger may move to `Discharged / Implementation Refined`.

A later target-portability reconciliation generalizes the proof predecessor used by SYS-016. The production Haskell surface was already target-neutral; only the proof aggregate had imported LLVM-specific runtime-symbol identity.

## Certified surface being extracted

The generalized Certified theorem composes `PHIL-SYS-RUNTIME-001` and target-neutral `PHIL-TARGET-RUNTIME-PRIM-001` and establishes five structural graph facts. `PHIL-LLVM-RUNTIME-SYM-001` remains an LLVM-specific refinement of the latter rather than a generic Systems predecessor.

### SYS-015 runtime claim/site graph

`decideRuntimeClaimGraphByFacts` owns the Certified requirement that every semantic runtime site is accepted by the selected runtime-evidence verifier. This predecessor relation already binds selected evidence, exact revision, and declared runtime cost.

Concrete claim/site domain construction, exact forward/reverse maps, source-obligation and source-fact derivation, site claiming, and physical-cost registry construction remain native finite-correspondence work.

### SYS-016 primitive/profile reuse

`decideRuntimePrimitiveReuseByFacts` owns two Certified facts:

1. site-owned contribution identity is injective, so reusing one primitive/profile cannot collapse distinct semantic sites; and
2. every target-visible runtime entry is accepted by `PHIL-TARGET-RUNTIME-PRIM-001`, whose identity depends on the physical primitive and selected target profile/signature rather than assurance metadata or claim cardinality.

The historical extracted constructor spelling `RuntimePrimitiveReuseSymbolIdentityDecision` is retained for kernel/API byte compatibility. It now denotes failure of the generic target-entry identity gate; it does not make a linker symbol part of Systems semantics.

Concrete profile selection, subject/site/profile maps, and backend entry representation remain outside this kernel. LLVM linker symbols, WebAssembly imports/functions/tables, VM opcodes/precompiles, and SBF syscall/CPI identities are target-profile refinements.

### SYS-018 cost attribution

`decideRuntimeCostAttributionByFacts` owns the Certified shared-charge compatibility rule: multiple contributions may share one final physical/accounting charge only when their selected cost class and cost shape agree exactly.

Concrete cost values and selected profile cost models remain explicit profile data rather than universal theorem content.

### Cumulative runtime graph

`decideSystemsRuntimeGraphByFacts` composes accepted SYS-015, SYS-016, and SYS-018 surfaces. The implementation-correspondence theorem proves that, under exact Boolean reflection hypotheses for the three groups, cumulative acceptance is equivalent to `RuntimeClaimCostGraphValid`.

## Explicit boundary

Concrete Haskell `Text`, key/revision, `Map`, `Set`, and list representation/enumeration; claim/site/subject/profile/contribution/charge graph construction; canonical stage revision serialization; exact diagnostic payloads; selected runtime evidence and profile truth; concrete numeric cost data; target entry/calling-convention/backend/runtime behavior; and Rocq/GHC correctness remain explicit correspondence/evidence/TCB boundaries.

## Staging verification

The existing `Phase 1 Systems Runtime Graph Proofs` workflow is extended to:

- compile `PHIL-TARGET-RUNTIME-PRIM-001`, the runtime evidence predecessor, generalized theorem, and implementation-correspondence theorem under Rocq 9.2.0;
- separately compile `PHIL-LLVM-RUNTIME-SYM-001` to ensure the existing LLVM backend remains a valid refinement;
- fresh-extract `SystemsRuntimeGraphKernel.hs` with Coq `bool` mapped directly to `Prelude.Bool`;
- require the extracted kernel surface to remain compatible with the production mirror;
- execute **12 direct controls** spanning SYS-015, SYS-016, SYS-018, and cumulative acceptance/failure classes;
- strict-typecheck the unchanged runtime graph implementation surfaces with their already-documented warning exemption; and
- rerun the unchanged **77-case** corpus: SYS-015 (17), SYS-016 (18), and SYS-018 (42).

The generalization changes proof authority, not the production decision vocabulary. A fully green re-certification is required before the existing `Implementation Refined` status is treated as preserved for the generalized theorem.
