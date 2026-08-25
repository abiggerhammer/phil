# Phase 1 provider replacement qualification v1

Status: implementation slice for `PROV-015`.

This slice implements the Phase 1 rule that provider replacement is a build/realization-time substitution between independently qualified provider subjects. Equality of the public provider contract does not transfer implementation-specific assurance lineage.

## Replacement pair

A replacement pair contains two independently checkable sides:

- predecessor qualification claim;
- predecessor evidence bundle;
- predecessor contextual admission;
- predecessor `ArchitectureInstance` and `ArchitectureRealization` revisions;
- replacement qualification claim;
- replacement evidence bundle;
- replacement contextual admission;
- replacement instance and realization revisions.

The checker re-runs the ordinary claim → evidence → admission identity check for both sides. It does not accept a predecessor checked result as the qualification of the replacement.

A valid replacement preserves:

- the exact required provider `InterfaceRevision`;
- the exact abstract provider occurrence;
- the exact `InstanceRevision`.

It changes:

- the qualification subject;
- `QualificationClaimRevision`;
- `QualificationEvidenceRevision`;
- `QualificationAdmissionRevision`;
- `RealizationRevision`.

The subject comparison works across semantic, concrete-realization, and collapsed-opaque qualification subjects. Replacing a checked Phil implementation with an independently admitted opaque provider is therefore representable at this identity/admission layer without pretending the two implementations share semantic identity.

## No evidence inheritance

The replacement evidence bundle is independently bound to the replacement claim revision. Supplying the predecessor evidence bundle directly therefore fails the ordinary evidence/claim binding check.

There is an additional explicit rule for evidence references that appear in both bundles. Shared references are rejected by default. Each deliberately shared reference needs a `ProviderReplacementEvidenceReuse` record that binds:

- the exact evidence-reference kind and reference value;
- the exact predecessor claim revision;
- the exact replacement claim revision;
- a non-empty validity-scope revision under which that evidence independently applies to both claims.

This models the Provider Qualification contract's distinction:

- implementation-specific proof/ABI/confinement/translation/etc. evidence is not inherited merely because two implementations satisfy the same contract;
- genuinely reusable evidence may be shared when its own exact validity scope independently applies to both qualification claims.

The checker does not prove the truth of an external validity-scope assertion. That remains evidence/admission assurance work. The important Phase 1 property here is that reuse is explicit and claim-bound rather than automatic inheritance.

## Realization semantics

Replacement preserves the abstract architecture occurrence while requiring a changed `RealizationRevision`. This matches ADR-020: implementation replacement is semantically invisible to `ArchitectureInstance` when the public binding remains fixed, but it is identity-bearing realization content.

This slice does not authorize live hot swap, private-state reinterpretation, persistent-state migration, handle continuity, or in-flight operation migration. Those require separate explicit migration/import/refinement contracts when needed.

## Conformance corpus

The dedicated harness covers:

- independently qualified replacement acceptance;
- exact provider occurrence/interface/instance preservation;
- changed claim/evidence/admission/realization lineage;
- predecessor evidence-bundle rejection;
- predecessor admission rejection;
- shared evidence without explicit scope rejection;
- explicit reusable evidence acceptance;
- empty/wrong reuse-scope binding rejection;
- same-subject non-replacement rejection;
- interface, occurrence, instance, and realization mismatch rejection;
- rejected replacement admission rejection; and
- semantic-to-collapsed-opaque replacement at the generic qualification identity layer.

## Deferred

This slice does not yet materialize Steve's concrete `DigestProvider` and `BlobProvider` qualification objects (`PROV-016`), construct complete `ArchitectureRealization` objects for both Phase 1 witnesses, prove provider-call correspondence into Systems/StageContract, or define source syntax for provider qualification/replacement.
