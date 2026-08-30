# Phase 1 Systems control preservation proof v1

Status: bounded Rocq certification tranche for `PHIL-SYS-CONTROL-001` over the already implemented/tested SYS-007–010 cumulative Systems/StageContract chain.

## Certified semantic surface

The proof in `proof/Phil/Core/SystemsControlPreservation.v` normalizes the four existing cumulative stage checkers into four explicit preservation relations.

### SYS-007 — branch resource/failure preservation

Accepted branch correspondence requires:

- exact reachable outcome domain;
- exact tracked-owner fate domain;
- every tracked owner fate realized exactly once;
- exact continuing/normal-terminal/fatal control classification; and
- tracked restricted values to denote owning values rather than scoped borrowed views.

The proof establishes that missing owner accounting, fabricated/multiple owner disposition, borrowed-view substitution, or control-class laundering cannot satisfy branch preservation.

### SYS-008 — join/loop state projection and closure capture

Accepted state projection requires:

- the exact boundary/projection kind;
- exact state-slot domain;
- exact restricted-owner mode;
- exact fixed semantic subject where required;
- unique restricted-owner projection;
- complete live-linear-owner coverage;
- no scoped-loan escape across the state boundary;
- exactly one carrier for each restricted closure capture; and
- no carrier sharing between distinct restricted captures.

The proof establishes fail-closed subject mismatch, restricted-owner duplication, and scoped-loan escape.

### SYS-009 — protocol-state succession

Accepted protocol correspondence requires:

- checked semantic correspondence rather than runtime transport coincidence;
- exact target site and transport use;
- exact outcome domain;
- exact protocol-instance and role identity;
- a fresh semantic successor endpoint occurrence;
- exactly-once predecessor consumption and successor production; and
- acyclic endpoint lineage.

The proof establishes that transport coincidence cannot substitute for semantic protocol correspondence and that stale predecessor reuse cannot be accepted as progression.

### SYS-010 — exact boundary commit correspondence

Accepted boundary correspondence requires:

- exact source runtime fact;
- exact transport;
- exact owning byte value and semantic subject;
- exact declared length relation;
- exact runtime-site kind and revision/evidence binding;
- exact protocol transition;
- commit outcome producing the protocol successor;
- failure outcome remaining terminal; and
- complete boundary emission/recognition before success progression.

The proof establishes fail-closed wrong-subject, wrong-length, and early-success cases.

## Cumulative theorem

`systemsControlPreserved` is the conjunction of all four stage relations. The aggregate theorems establish that a successful bounded SYS-007–010 chain retains branch ownership/control preservation, state projection/capture preservation, exact protocol lineage, and exact boundary commit progression simultaneously. In particular, successful aggregate verification cannot contain early boundary progression or stale/wrong protocol identity.

This composes semantically with the already Certified resource-loop, callable-mode, protocol-step, and boundary-progression obligations. The ledger dependency name `PHIL-SYS-OWN-001` is retained as a legacy aggregate alias; no new independent theorem is claimed under that identifier. The concrete ownership facts required here are represented directly by SYS-007 and SYS-008.

## Correspondence corpus

The dedicated workflow reruns the unchanged production corpora:

- `test/Phase1BranchResourceFailureMain.hs` — 12 SYS-007 cases;
- `test/Phase1ControlStateProjectionMain.hs` — 11 SYS-008 cases;
- `test/Phase1ProtocolStateCorrespondenceMain.hs` — 13 SYS-009 cases; and
- `test/Phase1BoundaryCommitCorrespondenceMain.hs` — 10 SYS-010 cases.

Total: **46 unchanged cases**.

## Explicit residual boundary

This is semantic certification, not implementation refinement. The following remain explicit boundaries:

- Rocq kernel/toolchain correctness;
- concrete Haskell `Text`, key/revision, `Map`, `Set`, and list equality/enumeration/extensional semantics;
- source/Core/StageContract to concrete Systems function/block/value/edge enumeration;
- CFG target/dominance and value-role correspondence outside the normalized semantic facts;
- exact owner/subject/endpoint occurrence representation and serialization;
- truth/competence of predecessor resource, callable, protocol, boundary, authority, evidence, provider, and realization facts supplied to the Systems chain;
- canonical stage-revision construction and content-addressing assumptions;
- diagnostic/error precedence and reconstruction; and
- Haskell implementation equivalence.

Physical scheduler/transport/runtime/backend correctness and target ABI/layout facts remain separate realization/provider evidence.

Baseline: `03d4a56b04f6f062adf5b7ed1208896ba66fa42f`.
