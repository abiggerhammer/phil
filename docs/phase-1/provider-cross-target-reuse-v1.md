# Phase 1 provider cross-target semantic reuse v1

This slice covers conformance case `PROV-013` from the Provider Qualification Checking and Schema Contract.

A pure Phil provider's semantic qualification is target-independent when its exact public provider interface and semantic implementation revision remain unchanged. Moving that already-qualified implementation to a different legal target does not require inventing a new semantic provider claim merely because representation, ABI, runtime support, or target assumptions changed.

The reusable identity is the exact `QualificationClaimRevision` from the Phase 1 claim/evidence/admission identity layer.

Target-specific realization evidence is a separate identity-bearing object. It binds that semantic claim to:

- the exact provider interface;
- the exact semantic implementation `DefinitionRevision`;
- one target-profile revision;
- one concrete artifact revision;
- one runtime/ABI revision;
- one realization-relation revision;
- explicit translation-validation evidence; and
- explicit target-specific assumptions.

Its revision is derived independently as `phil.provider-qualification.target-evidence.canonical.v1:...` using the existing canonical semantic-form encoding.

## Cross-target reuse rule

`checkProviderCrossTargetSemanticReuse` accepts only when:

1. the reusable claim is a semantic implementation qualification, not a concrete-realization or opaque-boundary claim;
2. both target evidence bundles bind the exact semantic claim revision;
3. both bind the exact required provider interface;
4. both bind the exact semantic implementation revision;
5. the old and new target profiles are distinct; and
6. each target evidence bundle carries explicit translation-validation evidence.

When those conditions hold, the semantic claim revision is preserved while the two target evidence revisions remain target-specific.

A target-specific assumption, ABI, artifact, realization relation, or translation-validation change therefore revises target evidence without revising the provider's semantic claim.

## Non-claims

This checker does not establish that a target is actually legal, prove the truth of translation-validation evidence, select an `ArchitectureRealization`, validate a concrete artifact/profile admission (`PROV-014`), govern replacement implementations or evidence inheritance (`PROV-015`), or lower provider evidence into a `StageContract`. Those remain separate Phase 1 obligations.
