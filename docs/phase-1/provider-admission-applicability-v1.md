# Phase 1 provider admission applicability v1

This slice covers conformance case **PROV-014** from the Provider Qualification Checking and Schema Contract.

## Purpose

An accepted provider qualification/admission is not ambient permission to use the provider anywhere that happens to link. It is applicable only to the exact concrete realization facts for which it was admitted.

This layer composes three already-distinct objects:

1. the accepted qualification/admission identity from PROV-011;
2. the target-specific realization evidence from PROV-013; and
3. the provider mapping actually selected by `ArchitectureRealization`.

The checker does not create another semantic provider claim. It checks whether an already accepted admission applies to one exact selected provider realization.

## Exact applicability binding

`ProviderConcreteAdmissionApplicability` binds:

- exact `QualificationAdmissionRevision`;
- exact semantic `QualificationClaimRevision`;
- exact target-realization evidence revision;
- exact provider-requirement occurrence;
- exact `InstanceRevision` being realized;
- exact `RealizationRevision`;
- exact required provider `InterfaceRevision`;
- exact selected implementation `DefinitionRevision`;
- exact target profile revision;
- exact artifact revision;
- exact runtime/ABI revision.

The target evidence supplied to the checker must itself reproduce the claim, interface, implementation, target, artifact, and ABI carried by the applicability binding.

The `SelectedProviderRealization` must then reproduce the applicability binding exactly.

## Symbols are not applicability

Exported/runtime symbols are deliberately carried only as nonsemantic metadata.

Therefore:

- equal symbol sets cannot make an admission for artifact/profile X applicable to selected realization Y; and
- changing a legal backend symbol alone does not invalidate an otherwise exact applicability relation.

This is the provider-admission counterpart of the architecture rule that realization selection cannot be reconstructed from what happens to link.

## Rejected admissions

A qualification admission whose decision is rejected cannot justify a selected realization, even when every artifact/profile/ABI field happens to match.

## Relation to ArchitectureRealization

The ArchitectureRealization contract requires the selected provider mapping to retain the exact provider requirement occurrence, selected implementation, qualification reference, target/ABI profile, and other identity-bearing realization choices.

PROV-014 checks the provider-qualification side of that relation before Systems/StageContract lowering.

## Deferred

This slice does not yet:

- govern replacement implementation evidence inheritance (PROV-015);
- materialize complete Steve DigestProvider/BlobProvider qualifications (PROV-016);
- construct a complete generic `ArchitectureRealization` object for both witnesses;
- prove Systems/StageContract provider-call correspondence (SYS-005);
- define final syntax; or
- provide a Rocq proof.
