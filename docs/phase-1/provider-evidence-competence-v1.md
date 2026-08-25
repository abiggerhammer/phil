# Phase 1 provider evidence-producer competence v1

Status: bounded executable conformance slice for `PROV-010`, generalized by the `PROV-016` Steve pressure case.

## Governing rule

A provider does not become competent to establish `Proof[P]` merely because one operation returns a value with that Phil type or computes bytes that happen to agree with an expected result.

For every evidence-producing provider operation, qualification must identify:

- the already-qualified public provider operation;
- the exact proposition family the operation is competent to establish;
- the exact semantic proposition parameters other than the stable subject;
- the exact stable semantic subject named by the proposition;
- the observation mechanism actually used by the implementation;
- the exact checked observation-to-subject mapping when the observation is not already the stable subject; and
- the exact validity contract under which the produced proposition remains usable.

The central rule remains:

> Observation identity is not evidence-subject identity.

A temporary borrow/view, raw pointer, runtime handle, or equal byte sequence does not become the semantic subject of a persistent proposition merely because it was the mechanism through which the provider observed the subject.

## Proposition parameters are not subjects

The Steve pressure case requires the checker to distinguish the two semantic roles in:

```text
DigestMatches(id, object)
```

`id` is a proposition parameter. `object` is the stable evidence subject. The implementation may observe `object` through a temporary borrowed byte view, but neither the borrow token nor `id` is the stable subject.

`ProviderEvidenceProducerRequirement` and `ProviderEvidenceProducerCompetenceClaim` therefore carry an exact ordered list of `RefTerm` proposition parameters separately from `ProviderEvidenceSubjectKey`.

The bounded checker materializes a Core proposition as:

```text
Atom proposition_family [parameter_1, ..., parameter_n, StableId provider-evidence-subject subject]
```

The observation key and loan scope are deliberately absent from that proposition.

The zero-parameter case is the original PROV-010 behavior and remains valid.

## Stable evidence subjects

`ProviderEvidenceSubjectKey` names the stable semantic subject of the resulting proposition. A digest provider may temporarily observe a scoped borrowed byte view while establishing a persistent proposition about the byte object that owns those bytes.

The temporary loan token is observation machinery, not the proposition subject.

## Observation forms

The checker distinguishes:

- `StableEvidenceObservation subject` — the implementation is already observing the exact stable semantic subject;
- `ScopedBorrowEvidenceObservation observation scope` — the implementation observes a temporary scoped borrow/view; and
- `OpaqueEvidenceObservation observation` — the observation mechanism is opaque to Phil and requires an explicit checked mapping.

A stable observation may use direct subject identity only when the observation and proposition subject are the same exact `ProviderEvidenceSubjectKey`.

Scoped or opaque observations require an explicit `CheckedObservationToStableSubject` mapping.

## Mapping is explicit

An observation mapping records the mapping revision, observed mechanism, and stable proposition subject. The checker requires its source to match the exact observation in the competence claim and its target to match the exact stable proposition subject required by the provider contract.

`RuntimeCoincidenceSubjectMapping` exists only as an explicit rejected form. Pointer equality, descriptor equality, borrow-token equality, handle equality, or equal runtime bytes are not semantic subject mappings by themselves.

The mapping revision is an assurance input. This slice checks exact binding and correspondence; it does not prove the truth of an external mapping theorem or certificate.

## Proposition family, parameters, and validity

The public provider requirement fixes one exact `ProviderPropositionFamilyKey`, one exact parameter list, and one exact `EvidenceValidityContractKey`. The competence claim must match all three exactly.

This prevents an implementation from silently changing the proposition family, retargeting a proposition parameter, or weakening the lifetime/validity conditions of the resulting evidence.

## Borrow lifetime versus evidence lifetime

Ending an observation loan does not inherently invalidate a proposition whose exact semantic subject is a stable owner and whose validity contract says the evidence persists beyond the observation.

Two different temporary borrows of the same stable byte object may therefore produce the same proposition identity when both checked mappings target the same stable subject and proposition parameters.

Conversely, mutating or replacing the stable subject may invalidate the proposition according to its validity contract. That policy is not encoded by temporary observation identity.

## Provider lineage

`checkProviderEvidenceProducerCompetence` consumes an already accepted `CheckedProviderSemanticQualification` and retains exact provider/implementation lineage, operation, proposition family and parameters, observation, stable subject, mapping, validity contract, and materialized proposition.

Provider replacement therefore does not inherit evidence competence accidentally.

## PROV-010 conformance pressure

The dedicated corpus covers scoped-borrow-to-owner mapping, rejection of loan identity as subject, wrong mapping targets, direct mapping misuse, runtime coincidence rejection, exact family and parameter matching, unqualified operations, exact validity, direct stable observations, borrow-identity noninterference, and provider-lineage retention.

The parameterized case specifically checks that a digest identifier remains a proposition parameter while the byte owner remains the stable evidence subject.

## Boundaries

This layer establishes competence shape and subject/parameter correctness. Truth of the proposition family, correctness of a cryptographic implementation, truth of external observation mappings, evidence/admission policy, and concrete artifact/ABI preservation remain ordinary later qualification and realization obligations.
