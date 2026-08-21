# Phil Phase 0 Plan: Semantic Decisions and Repository Foundation

## Objective

Produce a Phil specification package precise enough that two implementers could independently build compatible Phil Core checkers, and precise enough that rejected programs fail for stated semantic reasons rather than compiler accidents.

Phase 0 is governed by three complementary statements:

> **Phil is a systems language in which architecture is executable and implementation is replaceable.**

> **Phil constructs software top-down from boundaries, protocols, and obligations.**

> **Prototype → verify → rewrite → certify.**

The first states Phil's defining property, the second states its organizing method, and the third states its intended development workflow.

Phase 0 also adopts a performance pair:

> **Phil makes the cost of assurance explicit and erases assurance machinery that has completed its work.**

> **Proof should cost at compile time; uncertainty should cost at runtime.**

The first states Phil's cost objective; the second states how proof discharge and runtime checks divide responsibility.

## Working name

The language is provisionally named **Phil**. Phil is not an acronym. Phase 0 examples use the `.phil` extension so that syntax, diagnostics, and tooling can be evaluated under the name rather than treating naming as a detached branding exercise. Renaming remains possible before a public release.

## Work order

### 0.1 Freeze the demonstrator boundary

Use one binary framed-upload protocol. Keep the first transport synchronous and ordered. Do not include reconnection, message reordering, distributed persistence, or multiparty projection.

Deliverables:

- successful protocol source;
- role-local behavior sketches;
- accepted trace set;
- malformed-wire-input set;
- rejected-source corpus.

### 0.2 Settle the core judgments

Accepted semantic judgment:

```text
Σ ; Γ ; A ; Δ ⊢ P :: (c : S) ▷ Φ
```

Interpretation:

- `Σ`: immutable Core declarations/contracts;
- `Γ`: unrestricted values and declarations;
- `A`: affine resources, usable at most once;
- `Δ`: linear resources, consumable exactly once;
- `P`: checked process or component body;
- `c : S`: endpoint or result provided by `P`;
- `Φ`: named residual refinement/evidence/boundary obligations.

The normative semantic presentation is provider-oriented. The first executable checker uses equivalent bidirectional residual-resource judgments as specified by ADR-001 and `docs/semantics/core-judgments.md`.

### 0.3 Define observable behavior

The reference semantics must emit a stable trace vocabulary, not arbitrary debug strings. Initial events:

```text
SessionOpened
MessageRecognized(grammar, span)
MessageRejected(grammar, failure)
ValueValidated(policy)
ValueRejected(policy, failure)
BranchSelected(label)
BytesTransferred(count)
SessionClosed(outcome)
SessionFailed(class, detail)
ResourceConsumed(resource_id)
BoundaryEscalated(obligation)
```

Internal computation is unobservable unless it changes one of these events.

### 0.4 Define proof and test boundaries

For every property, classify evidence as one of:

- kernel-checked;
- proof-assistant theorem;
- translation-validated;
- differential-tested;
- property-tested;
- runtime-enforced;
- assumed.

No document may say merely “verified” without naming the level.

### 0.5 Define the first cost model

Accepted ADR-011 fixes the Phase 0 runtime representation and cost discipline.

The cost model now distinguishes:

- source-semantic runtime work;
- runtime-assurance-required checks;
- target/ABI requirements;
- checked-runtime defensive instrumentation;
- conservative lowering residue that is not semantically required.

Certified release erases proof/typestate/borrow machinery only after its lowering facts are transferred, while retaining all accepted runtime-bound enforcement mechanisms.

Deliverables:

- attributable-cost rule — accepted;
- checked-runtime and certified-release policies — accepted;
- first lowering-ledger cost/representation fields — accepted;
- upload runtime/cost representation witness — accepted;
- negative lowering/cost conformance cases — accepted;
- demonstrator benchmark and inspection dimensions — fixed;
- exact systems-language comparison baseline — to be selected before measurements, not a semantic blocker.

### 0.5a Fix the property-directed lowering boundary

Accepted ADR-007 fixes four required competence layers:

```text
Phil Core
Protocol & Boundary semantics
Systems representation
Backend / target representation
```

These are semantic competence contracts rather than a required count of serialized IRs. Adjacent layers may share a physical representation only when both contracts remain inspectable and verifiable.

Deliverables:

- fact-transfer rule — accepted;
- per-layer competence and non-competence boundaries — accepted;
- stage-contract schema — accepted;
- upload stage-contract witness — accepted;
- cross-stage lowering negative cases — accepted;
- custom MLIR made optional rather than semantic architecture — accepted.

### 0.6 Review the eleven ADRs

Recommended review order:

1. ADR-009 — demonstrator protocol
2. ADR-004 — recognition and validation
3. ADR-005 — failure and cancellation
4. ADR-003 — binary session calculus
5. ADR-002 — structural modes
6. ADR-006 — refinement language
7. ADR-001 — semantic foundation
8. ADR-010 — assurance ledger
9. ADR-011 — runtime representation and cost semantics
10. ADR-007 — IR architecture
11. ADR-008 — LLVM boundary

All eleven ADRs are accepted. The ordered Phase 0 ADR review is complete.

This order starts from behavior and works inward toward theory and implementation.

## Phase 0 exit criteria

Phase 0 is complete when:

1. every surface construct in the demonstrator has an intended core elaboration;
2. every accepted trace is explainable from the operational semantics;
3. every rejected example names the earliest competent rejecting layer;
4. failure and cancellation consume or transform every live linear resource explicitly;
5. recognition success implies complete membership in the declared input language;
6. the trusted-computing-base statement is concrete enough to audit;
7. no unresolved question blocks a minimal synchronous Phil Core checker;
8. the demonstrator's architecture has executable meaning independent of any one component implementation;
9. acceptance criteria for an independently written rewrite are stated in terms of obligations and observable traces rather than source similarity;
10. every retained runtime cost is classified as source-semantic, runtime-assurance-required, target-required, defensive-profile, or conservative lowering, with the required ADR-010/ADR-011 cross-links;
11. every erased proof/check/typestate mechanism has an accepted assurance basis and a lowering decision showing how its still-live invariant is preserved;
12. the initial performance comparison and inspection method are specified before code generation begins;
13. every obligation in the declared certification scope is present in an assurance manifest whose acceptance rule is satisfied, assumptions/exports are explicit, runtime enforcement is mapped, and no in-scope obligation is unresolved;
14. every lowering competence boundary has a stage contract showing which facts are consumed, transferred, erased, or turned into derived obligations, and local IR well-formedness is never treated as sufficient evidence of cross-stage preservation;
15. LLVM emission records every optimizer-strengthening fact with artifact-scoped evidence, retains all runtime-bound mechanisms, distinguishes pre-optimization/optimized/native assurance scopes, and makes LLVM/toolchain assumptions explicit for any certified native artifact.

## Phase 0 ADR review completion

All eleven ADRs are accepted. No unresolved semantic decision blocks implementation of the minimal synchronous Phil Core checker.

The next implementation sequence is:

1. implement the Core parser/elaborator/checker against the accepted positive/negative corpus;
2. implement or expose the protocol/boundary semantic graph needed by the demonstrator;
3. only then begin the systems/backend lowering track, using ADR-007/011 stage contracts;
4. treat backend/target -> pre-optimization LLVM as the first translation-validation priority under ADR-008.

The exact implementation language, physical IR serialization, optional MLIR use, and later native-code validation depth remain engineering choices rather than semantic blockers.

## Questions that may remain open after Phase 0

These may be deferred if they do not affect the demonstrator:

- whether a future post-Phase-0 example justifies adding a primitive relevant mode beyond ADR-002's accepted three-mode discipline;
- exact proof-theoretic shifts/polarities for general higher-order value connectives beyond ADR-001's accepted session-head polarity;
- exact physical proof/evidence retention strategy beyond ADR-011's accepted rule that runtime-irrelevant machinery erases only after lowering consumers have received the fact;
- whether the implementation language is Haskell, OCaml, or another typed functional language;
- whether the first implementation uses custom Phil MLIR dialects at all, and if so at which phase;
- whether authority modalities enter the first executable slice;
- target/profile-specific defensive assertions beyond the accepted checked-runtime versus certified-release split;
- which systems-language implementation serves as the first performance baseline.
