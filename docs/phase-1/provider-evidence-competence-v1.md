# Phase 1 provider evidence-producer competence v1

Status: bounded executable conformance slice for `PROV-010`.

## Governing rule

A provider does not become competent to establish `Proof[P]` merely because one operation returns a value with that Phil type or computes bytes that happen to agree with an expected result.

For every evidence-producing provider operation, qualification must identify:

- the already-qualified public provider operation;
- the exact proposition family the operation is competent to establish;
- the exact stable semantic subject named by the proposition;
- the observation mechanism actually used by the implementation;
- the exact checked observation-to-subject mapping when the observation is not already the stable subject; and
- the exact validity contract under which the produced proposition remains usable.

The central Phase 1 rule is:

> Observation identity is not evidence-subject identity.

A temporary borrow/view, raw pointer, runtime handle, or equal byte sequence does not become the semantic subject of a persistent proposition merely because it was the mechanism through which the provider observed the subject.

## Stable evidence subjects

`ProviderEvidenceSubjectKey` names the stable semantic subject of the resulting proposition.

The bounded checker materializes a Phil Core proposition as:

```text
Atom proposition_family [StableId provider-evidence-subject subject]
```

The observation key and loan scope are deliberately absent from that proposition.

This makes the intended Steve digest pressure case precise. A digest provider may temporarily observe a scoped borrowed byte view while establishing a persistent proposition about the byte object that owns those bytes:

```text
DigestMatches(..., byte_object)
```

The temporary loan token is observation machinery, not the proposition subject.

## Observation forms

The first checker distinguishes:

- `StableEvidenceObservation subject` — the implementation is already observing the exact stable semantic subject;
- `ScopedBorrowEvidenceObservation observation scope` — the implementation observes a temporary scoped borrow/view; and
- `OpaqueEvidenceObservation observation` — the observation mechanism is opaque to Phil and requires an explicit checked mapping.

A stable observation may use direct subject identity only when the observation and proposition subject are the same exact `ProviderEvidenceSubjectKey`.

Scoped or opaque observations require an explicit `CheckedObservationToStableSubject` mapping.

## Mapping is explicit

An observation mapping records:

```text
mapping revision
observed subject/mechanism
stable proposition subject
```

The checker requires the mapping source to match the exact observation in the competence claim and its target to match the exact stable proposition subject required by the provider contract.

`RuntimeCoincidenceSubjectMapping` exists only as an explicit rejected form. Claims such as:

- same pointer;
- same file descriptor;
- same borrow token;
- same machine handle; or
- same runtime bytes

are not semantic subject mappings by themselves.

The mapping revision is an assurance input. This slice checks exact binding and correspondence; it does not prove the truth of an external mapping theorem or certificate.

## Proposition family and validity

The public provider requirement fixes one exact `ProviderPropositionFamilyKey` and one exact `EvidenceValidityContractKey`.

The competence claim must match both exactly.

This prevents an implementation from silently changing:

- which proposition family it claims competence for; or
- the lifetime/validity conditions of the resulting evidence.

In particular, a provider whose public competence says evidence persists according to stable-owner validity cannot silently substitute a loan-only validity contract merely because the implementation observed a temporary borrow.

## Borrow lifetime versus evidence lifetime

Ending an observation loan does not inherently invalidate a proposition whose exact semantic subject is a stable owner and whose validity contract says the evidence persists beyond the observation.

Two different temporary borrows of the same stable byte object may therefore produce the same proposition identity when both checked mappings target the same stable subject.

Conversely, mutating or replacing the stable subject may invalidate the proposition according to its validity contract. That policy is not encoded by the temporary observation identity.

## Provider lineage

`checkProviderEvidenceProducerCompetence` consumes an already accepted `CheckedProviderSemanticQualification`.

The checked competence result retains:

- exact provider `InterfaceRevision`;
- exact implementation `DefinitionRevision`;
- exact evidence-producing provider operation;
- exact proposition family;
- exact observation;
- exact stable proposition subject;
- exact subject mapping;
- exact validity contract; and
- the materialized Core proposition.

This means provider replacement does not inherit evidence competence accidentally. A new implementation must obtain its own qualification/evidence lineage even if it satisfies the same public provider contract.

## PROV-010 conformance pressure

The dedicated corpus covers:

1. a scoped borrow explicitly mapped to the stable owner subject;
2. rejection when the temporary borrow token is substituted for that owner subject;
3. rejection when an explicit mapping targets the wrong stable subject;
4. rejection when a scoped borrow attempts direct stable-subject identity;
5. rejection of pointer/byte/runtime coincidence as a semantic mapping;
6. exact proposition-family matching;
7. evidence production only through an already-qualified provider operation;
8. exact validity-contract matching;
9. direct identity for an observation that is already the stable subject;
10. identical proposition identity from distinct temporary borrows of the same stable owner; and
11. retention of exact provider contract and implementation lineage.

## Boundaries and deferred work

This slice establishes competence shape and stable-subject correctness only.

It does **not** yet establish:

- truth of the proposition family itself;
- universal correctness of a cryptographic implementation;
- truth of an external observation-to-subject mapping;
- generic ProviderQualification evidence/disposition closure;
- proof/certificate acceptance policy;
- qualification dependency-cycle checking;
- contextual build admission;
- ArchitectureRealization provider selection;
- concrete artifact/ABI/StageContract preservation;
- final provider/evidence source syntax; or
- Rocq proof of PROV-010.

Those remain explicit later assurance/realization obligations rather than being smuggled into evidence-subject identity.
