# Phase 1 Systems evidence-preservation proof v1

This slice certifies `PHIL-SYS-EVID-001`, the aggregate SYS-011–013 evidence, erasure, and assumption-preservation obligation.

## SYS-011 — evidence follows semantic subjects only through exact transfer

The proof does not duplicate the subject-transport theory. It composes the already Certified `PHIL-BND-SUBJECT-001`, which in turn composes `PHIL-DATA-SUBJECT-001`.

A changed semantic subject can carry prior evidence only through the explicit checked transport plus the boundary copy gates: exact copy kind, copy-relation revision, byte-equality revision, proposition-specific transfer-law revision, exact evidence reference, and validity-scope revision. Runtime coincidence remains non-authoritative.

## SYS-012 — erasure requires discharge and consumer closure

An accepted evidence erasure requires:

- an exact accepted in-scope Assurance erasure use;
- at least one selected usable evidence entry for the exact obligation revision;
- exact binding of the source fact to the semantic subject;
- exact binding of the discharge evidence to that same semantic subject;
- a nonempty erased-representation identity;
- an explicit last semantic use;
- an explicit no-later-consumer basis;
- well-formed optional successor-invariant, runtime-residue-change, and cost-change revisions; and
- closure of every modeled later consumer.

A later consumer that still needs the erased representation rejects. A later consumer may instead use the exact declared successor invariant, but a missing or different successor invariant rejects. The last semantic use cannot reappear as a later consumer.

The Assurance side is imported from Certified `PHIL-ASSURE-USE-001`; this proof therefore does not silently weaken an Assurance erasure into a local Systems-only deadness test.

## SYS-013 — assumption dependencies remain exact and bidirectional

For every assumption inherited by a source fact, Systems mechanism, or SYS-012 erasure, the proof requires:

- the exact assumption to exist in the registry iff some consumer requires it;
- the registered assumption to carry Certified `PHIL-ASSURE-ASSUME-001` authority;
- a nonempty validity-scope revision;
- an exact forward dependency edge from every required consumer;
- the exact registered validity-scope revision on that forward edge; and
- the exact reverse edge from the assumption back to every required consumer.

Thus retaining only an assumption name, dropping its scope, omitting a fact/mechanism/erasure edge, or omitting the reverse dependency cannot satisfy the aggregate relation.

## Aggregate theorem

`systems_evidence_preservation_is_cumulative` requires the SYS-011 subject transfer, SYS-012 erasure relation, and SYS-013 assumption relation simultaneously. Successful aggregate preservation therefore yields an exact valid copy transport while retaining the complete erasure and assumption-preservation obligations.

## Correspondence evidence

The dedicated workflow reruns the unchanged implementation corpus:

- `test/Phase1EvidenceSubjectTransferMain.hs` — 11 SYS-011 cases;
- `test/Phase1EvidenceErasureMain.hs` — 12 SYS-012 cases; and
- `test/Phase1AssumptionDependencyMain.hs` — 13 SYS-013 cases.

Total unchanged correspondence corpus: **36 cases**.

## Explicit residual boundary

This certificate does not mechanize:

- concrete Haskell `Text`, `Map`, `Set`, or list equality/ordering/enumeration;
- canonical Systems stage-revision serialization or hashing;
- derivation/completeness of the concrete source-fact, subject, consumer, or assumption maps;
- truth or competence of selected evidence beyond the already-Certified Assurance verifier gates;
- concrete diagnostic precedence and payloads;
- Haskell implementation equivalence; or
- Rocq kernel/toolchain correctness.

Those remain explicit implementation-correspondence, evidence, or TCB boundaries.

Baseline at proof-branch cut: `1ebf03297def8a2e8f681f52329ee0369969664b`.