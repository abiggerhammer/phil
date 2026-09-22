# PHIL-AUD-PREREQUISITE-SUPPORT-001 implementation handoff

This handoff tracks the Haskell correspondence work following the prerequisite-support proof landed in #1298.

## Repaired prerequisite relation

`Phil.Core.Discharge.resolveObligation` can make a locally established prerequisite available to a later decision certificate as `PrerequisiteFact childId`. The assurance handoff traverses the retained `DecisionCertificate`, resolves every such obligation ID against the complete flattened `ResolvedObligation` tree, and records the exact child revision as `DependsOnObligation` support.

The support direction is explicit:

- certificate consumer revision -> prerequisite revision.

Generation provenance remains unchanged:

- generated child revision -> parent revision in `revisionGeneratedFrom`.

`handoffSupportEdges` projects only the obligation-support relation as `(consumer, prerequisite)` pairs. It does not reverse or reinterpret lineage.

#1306 carried that distinction into `buildVerificationRevisionGraphWithSupport`: historical generation lineage is no longer treated as semantic support. #1309 then bound the explicit handoff support into final certificate `EvidenceEntry` values and rebound their evidence digest.

## EvidenceFact identity correspondence

A retained Core certificate may also depend on `EvidenceFact bindingName factIndex`. Those names and indices are local Core references, not immutable assurance-ledger identities. `handoffResolvedObligationWithEvidence` now requires the assurance boundary to supply an explicit map from `(Name, Int)` to `EvidenceEntryId` and translates each retained `EvidenceFact` to `DependsOnEvidence`.

The ordinary `handoffResolvedObligation` route supplies no such map. If a certificate retains an `EvidenceFact`, that route now fails closed rather than silently dropping the dependency.

Once the handoff has resolved both support classes, `bindHandoffCertificateEvidence` treats the handoff relation as authoritative. Caller-supplied `DependsOnEvidence` and `DependsOnObligation` edges are replaced by the exact dependencies retained by the certificate and the evidence digest is rebound. Precise evidence-entry support remains distinct from whole-obligation support: only the latter is projected into the revision support graph.

## Fail-closed behavior

A certificate that names a `PrerequisiteFact` absent from the resolved handoff tree returns `UnknownPrerequisiteSupport`. A certificate that names an `EvidenceFact` without an immutable evidence-entry mapping returns `UnknownEvidenceFactSupport`.

Prerequisite resolution uses the whole flattened tree rather than only direct children. This is required because prerequisite resolution is left-to-right: a later sibling certificate may rely on an earlier locally established sibling.

## Permanent controls

The assurance handoff controls cover:

- unchanged child-to-parent `revisionGeneratedFrom` provenance;
- explicit parent/consumer-to-child `DependsOnObligation` support;
- no accidental reversed support edge;
- later-sibling support of an earlier sibling;
- fail-closed rejection of a missing prerequisite revision;
- exact `EvidenceFact` -> `DependsOnEvidence` translation;
- fail-closed rejection of an unmapped evidence fact;
- replacement of stale caller-supplied certificate dependencies by the authoritative handoff relation; and
- preservation of the distinction between precise evidence dependencies and revision-graph support.

Existing runtime/export handoff controls remain in place.

## Remaining correspondence

The remaining production correspondence is the INT-002/manifest consumer hookup: the shipped manifest-closure path must consume these exact handoff-bound `EvidenceEntry` values and their prerequisite/evidence dependencies rather than reconstructing or accepting a parallel relation. That should remain a separate slice so the final-consumer authority can be reviewed directly.

No LLVM behavior or other Phase 1 trusted-computing-base component is changed or audited here.
