# Phase 1 boundary subject-transfer proof v1

This slice certifies `PHIL-BND-SUBJECT-001`, covering the semantic core of BND-012 byte-subject evidence transfer and BND-013 zero-copy target correspondence.

## BND-012 — changed byte subjects require exact transfer

The Rocq proof imports the already Certified `Phil.Core.DataSubject` theory rather than restating stable-subject semantics. A boundary copy transfer is accepted only alongside an explicit checked DATA-SUBJECT transport, and adds exact boundary-specific facts:

- the underlying transport is a copy transport;
- a concrete copy-relation revision is present;
- an exact byte-equality revision is present;
- a proposition-specific evidence-transfer-law revision is present;
- the allowed evidence reference is exactly the evidence being rebound; and
- an explicit validity-scope revision is present.

The composition theorem uses `checked_explicit_transport_is_valid` from `DataSubject.v`, so an accepted boundary transfer inherits the certified DATA-SUBJECT requirements for exact prior/replacement identities, source/target propositions, relation revision, evidence reference, and accepted transport status.

Runtime representation coincidence is represented only as an invalid candidate and can never authorize transfer. Missing copy, byte-equality, transfer-law, or validity-scope identity also rejects.

## BND-013 — zero-copy is a checked realization relation

A zero-copy realization is accepted only when:

- its relation is bound to the exact target-strengthening stage revision;
- exact BoundaryRepresentation, grammar, and semantic value-type revisions are present;
- source semantic layout correspondence is present;
- concrete target memory layout correspondence is present;
- endian/alignment/padding/tagging correspondence is present;
- lifetime rules are present;
- ownership/borrowing rules are present;
- device/storage-domain constraints are present; and
- target assumptions/carriers are present.

Pointer reinterpretation alone is explicitly invalid. The proof treats these correspondence facts as named imported identities; it proves that an accepted zero-copy relation requires them, not that any particular ABI/layout/lifetime proposition is true.

## Correspondence evidence

The dedicated workflow re-runs the unchanged implementation corpus:

- `test/Phase1EvidenceSubjectTransferMain.hs` — 11 SYS-011/BND-012 cases covering explicit relation requirement, checked copy acceptance, runtime-coincidence rejection, exact relation endpoints, exact source evidence, proposition-specific transferability, unknown/missing relation rejection, nonempty evidence, and deterministic stage identity;
- `test/Phase1BoundaryTargetRelationMain.hs` — 4 BND-013 cases covering complete zero-copy acceptance, missing endian/alignment rejection, stale-stage rejection, and pointer-reinterpretation rejection.

Total unchanged correspondence corpus: 15 cases.

## Explicit residual boundary

This certificate does not mechanize:

- concrete Haskell `Text`, `Map`, or `Set` representation/equality/ordering;
- canonical Haskell stage-revision construction;
- truth of a declared copy relation, byte-equality fact, or proposition-specific transfer law;
- concrete source-evidence membership and transferability computation;
- the predecessor target-strengthening implementation or the truth of concrete ABI/layout/endian/alignment/padding/tagging/lifetime/ownership/device-storage/assumption facts;
- Haskell implementation equivalence; or
- Rocq kernel/toolchain correctness.

Those remain explicit correspondence, target-evidence, implementation-refinement, or TCB boundaries.

Baseline at proof-branch cut: `a603c156d2d0f24564767b9167503248c1085ccd`.
