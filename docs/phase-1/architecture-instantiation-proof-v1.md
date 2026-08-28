# Phase 1 architecture instantiation proof v1

This note records the Rocq proof tranche for logic-ledger obligation `PHIL-ARCH-INST-001` and conformance cases ARCH-005, ARCH-006, ARCH-008, and ARCH-009.

## Certified semantic surface

`proof/Phil/Core/ArchitectureInstantiation.v` builds directly on the Certified `PHIL-ARCH-ID-001` model and proves the bounded architecture-instantiation algebra already exercised by production.

### Generative occurrence identity

A new child occurrence is keyed by the exact pair of stable parent occurrence and stable child slot. The proof establishes:

- distinct slots under one parent generate distinct child occurrence keys;
- the same child slot under distinct parent occurrences generates distinct child occurrence keys;
- distinct occurrence keys induce distinct instance identities even when declaration identity and static bindings are otherwise equal; and
- changing identity-bearing static bindings preserves stable occurrence lineage while revising exact instance identity.

These are the representation-neutral ARCH-005/ARCH-006 generativity rules.

### Explicit sharing

An explicit architecture reference resolves to the already named `InstanceKey`; it does not generate a second occurrence. Reference acceptance separately requires that the exact named target exist in the checked graph.

### Explicit requirement closure

The requirement decision model contains no ambient candidate-selection path and no privileged root path. A requirement with no explicit architecture disposition remains unresolved regardless of what candidate facts may exist elsewhere.

For a `BoundTo`-style disposition, the ordered checks are:

1. an explicit disposition must exist;
2. the named target occurrence must exist; and
3. when the concrete checker reflects an exact interface requirement, that interface must match.

Non-binding explicit dispositions such as static satisfaction, runtime binding, assumption, re-export, or deployment export are already explicit architecture boundaries and therefore close the architecture-level requirement without implicit search.

This captures the bounded ARCH-008/ARCH-009 rule: root authority is explicit, singular requirements are never filled by ambient dependency injection, and exact provider/callable-style bindings remain revision checked.

## Correspondence boundary

The Rocq theorem intentionally does not certify concrete graph implementation machinery. The following remain explicit implementation/correspondence foundations:

- Text-backed `InstanceKey`, `OccurrenceSlotKey`, requirement, and reference keys;
- `Map` normalization, lookup, traversal, and duplicate detection;
- construction and validation of the finite `ArchitectureInstanceGraph`;
- canonical `SemanticForm` serialization and concrete `InstanceRevision` bytes;
- source occurrence-site elaboration and environment lookup; and
- the truth of reflected target-existence and exact-interface facts.

No runtime initialization authority is modeled or granted by this proof.

## Dedicated gate

`Phase 1 Architecture Instantiation Proofs`:

- recompiles the Certified architecture identity dependency;
- compiles `ArchitectureInstantiation.v` under Rocq 9.2.0;
- records source and `.vo` SHA-256 identities in a proof-certificate artifact;
- typechecks the existing `Phil.Core.Static` architecture path and unchanged `Phase1ArchitectureInstantiationMain.hs` corpus under `-Wall -Werror`; and
- reruns all 11 existing ARCH-005/006/008/009 pressure cases unchanged.

Mechanical production correspondence beyond the unchanged executable pressure corpus remains a separate later implementation-refinement obligation.
