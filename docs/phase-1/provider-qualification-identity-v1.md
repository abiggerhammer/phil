# Phase 1 Provider Qualification Identity Layers v1

This slice implements conformance case `PROV-011`: provider qualification claim, evidence, and admission are three distinct identity layers.

The governing rule is:

> A ProviderQualification states an exact conditional refinement claim. Evidence justifies the claim; build admission decides whether its conditions are acceptable here.

Phase 1 therefore derives three separate canonical revisions.

## QualificationClaimRevision

The claim revision identifies the conditional semantic statement. Its identity includes:

- the exact required provider `InterfaceRevision`;
- the exact qualification subject:
  - semantic implementation `DefinitionRevision`,
  - semantic implementation plus exact concrete artifact for concrete realization qualification, or
  - exact opaque artifact/service/runtime boundary;
- the qualification layer;
- normalized semantic refinement relations;
- exact conditional requirements/assumptions represented as claim conditions; and
- the exact validity-scope predicate.

The claim revision deliberately excludes evidence-file bytes, proof/certificate references, current assurance policy, one build's selected dependency admissions, and one build's accept/reject decision.

Consequently, two different evidence bundles may justify the same exact qualification claim without changing `QualificationClaimRevision`.

## QualificationEvidenceRevision

The evidence revision identifies one exact evidence/disposition bundle for one exact claim revision. Its identity includes:

- exact `QualificationClaimRevision`;
- exact normalized obligation dispositions;
- evidence references;
- proof/certificate references;
- translation-validation references;
- runtime-enforcement references;
- assumption references; and
- validity dependencies.

Replacing one proof or certificate with another accepted proof of the same semantic claim therefore changes `QualificationEvidenceRevision` while preserving `QualificationClaimRevision`.

Map/set insertion order is nonsemantic.

## QualificationAdmissionRevision

Admission is contextual. Its identity includes:

- exact claim revision;
- exact evidence revision;
- exact provider occurrence being realized;
- exact required provider interface;
- exact realization-context revision;
- exact assurance-policy revision;
- exact condition dispositions;
- exact dependency admissions;
- selected artifact/runtime/ABI identity when fixed by the build;
- exported runtime obligations;
- exported deployment requirements; and
- the admission decision and rejection reasons.

The same closed conditional qualification may therefore be admitted by one build policy and rejected by another without mutating the semantic claim or evidence bundle.

## Canonical representation

This slice reuses `Phil.Core.Static.SemanticForm` and `canonicalSemanticForm` rather than introducing another serializer. Revisions are inspectable Phase 1 values:

- `phil.provider-qualification.claim.canonical.v1:...`
- `phil.provider-qualification.evidence.canonical.v1:...`
- `phil.provider-qualification.admission.canonical.v1:...`

The final compact digest/byte encoding remains deferred. Any later compact encoding must preserve the equality relation established by these canonical semantic forms.

## Binding checks

The checker rejects:

- an evidence bundle whose claim revision does not match the exact semantic claim;
- an admission whose claim revision does not match the claim;
- an admission whose evidence revision does not match the supplied evidence bundle; and
- an admission whose required provider interface differs from the semantic claim.

These checks prevent accidental evidence/admission reuse across unrelated provider qualifications.

## Conformance corpus

`test/Phase1ProviderQualificationIdentityMain.hs` covers:

- different evidence bundles preserving claim revision;
- different evidence bundles receiving different evidence revisions;
- evidence references never entering claim identity;
- semantic claim changes revising claim identity;
- deterministic evidence ordering;
- evidence-content changes revising evidence identity;
- policy changes preserving upstream claim/evidence identity;
- policy changes revising admission identity;
- decision changes revising admission identity;
- deterministic admission ordering;
- evidence/claim binding mismatch rejection;
- admission/evidence binding mismatch rejection; and
- admission/interface mismatch rejection.

## Deliberate limits

This slice establishes the identity separation required by `PROV-011`. It does not yet close generic qualification obligations, validate evidence truth, reject ungrounded dependency cycles (`PROV-012`), define cross-target semantic reuse (`PROV-013`), check artifact/profile applicability (`PROV-014`), implement replacement/no-inheritance semantics (`PROV-015`), materialize Steve provider qualifications (`PROV-016`), select providers in `ArchitectureRealization`, define final source syntax, or provide Rocq proof.
