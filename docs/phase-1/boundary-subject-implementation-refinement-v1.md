# PHIL-BND-SUBJECT-001 implementation refinement — staging v1

`PHIL-BND-SUBJECT-001` is already Certified by `proof/Phil/Core/BoundarySubject.v` and composes the Certified DATA-SUBJECT transport semantics.

This staging slice extracts only the boundary-specific decision authority. Production is unchanged.

## Extracted decisions

`proof/Phil/Core/BoundarySubjectImplementation.v` defines two representation-neutral decision surfaces.

### Boundary subject transfer

`decideBoundarySubjectTransferByFacts` owns the ordered boundary-specific admission gates for an explicit transfer:

1. checked transfer rather than runtime subject coincidence;
2. copy transport kind;
3. nonempty copy-relation revision;
4. nonempty exact byte-equality revision;
5. nonempty evidence-transfer-law revision;
6. exact evidence-reference authorization; and
7. nonempty validity-scope revision.

The Rocq correspondence theorem proves that the accepted decision over facts reflected from a Certified `BoundarySubjectTransfer` is equivalent to `BoundarySubjectTransferAccepted`.

The underlying DATA-SUBJECT transport remains a predecessor obligation and is not duplicated by this kernel.

### Zero-copy target realization

`decideZeroCopyRealizationByFacts` owns the ordered BND-013 gates:

1. checked zero-copy relation rather than pointer reinterpretation;
2. exact target-strengthening stage revision;
3. boundary-representation revision;
4. grammar revision;
5. semantic value-type revision;
6. source semantic-layout fact;
7. concrete memory-layout fact;
8. endian/alignment/padding/tagging fact;
9. lifetime-rules fact;
10. ownership/borrowing-rules fact;
11. device/storage-domain constraints fact; and
12. target assumptions/carriers fact.

The Rocq correspondence theorem proves accepted reflected facts equivalent to Certified `ZeroCopyRelationAccepted`.

## Explicit native/reflection boundaries

The following remain outside the extracted kernel:

- concrete Haskell `Text`, `Map`, `Set`, newtype, and identity representation;
- canonical stage-revision derivation;
- iteration order needed to reconstruct exact production diagnostics;
- truth and competence of copy/equality/transfer-law evidence;
- target-profile layout, endian/alignment, lifetime, ownership, device/storage, and assumptions facts;
- predecessor subject-correspondence and target-strengthening verification;
- concrete diagnostic payload construction; and
- GHC/runtime correctness.

## Staging validation

The registered `Phase 1 Boundary Subject Proofs` workflow is extended additively to compile the Certified predecessor/proof plus implementation correspondence, fresh-extract `BoundarySubjectKernel.hs`, strict-typecheck and run direct decision controls, strict-typecheck the unchanged BND-012/BND-013 production modules, rerun the unchanged 15-case correspondence corpus, and record staging identities.

A green staging PR leaves the ledger at `Discharged / Certified`. A separate closeout PR must check in the exact extracted kernel and bind production decisions before promotion to `Implementation Refined`.
