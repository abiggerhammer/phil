# PHIL-AUD-PREREQUISITE-SUPPORT-001 implementation handoff

This slice implements the first Haskell correspondence step for the prerequisite-support proof landed in #1298.

## Repaired relation

`Phil.Core.Discharge.resolveObligation` can make a locally established prerequisite available to a later decision certificate as `PrerequisiteFact childId`. The assurance handoff now traverses the retained `DecisionCertificate`, resolves every such obligation ID against the complete flattened `ResolvedObligation` tree, and records the exact child revision as `DependsOnObligation` support.

The support direction is therefore explicit:

- certificate consumer revision -> prerequisite revision.

Generation provenance remains unchanged:

- generated child revision -> parent revision in `revisionGeneratedFrom`.

`handoffSupportEdges` projects only the former relation as `(consumer, prerequisite)` pairs. It does not reverse or reinterpret lineage.

## Fail-closed behavior

A certificate that names a `PrerequisiteFact` absent from the resolved handoff tree now causes `handoffResolvedObligation` to return `UnknownPrerequisiteSupport` instead of silently emitting a handoff that has lost the certificate's support authority.

Support resolution uses the whole flattened tree rather than only direct children. This is required because prerequisite resolution is left-to-right: a later sibling certificate may rely on an earlier locally established sibling.

## Permanent controls

`AssuranceHandoffMain` now checks:

- unchanged child-to-parent `revisionGeneratedFrom` provenance;
- explicit parent/consumer-to-child `DependsOnObligation` support;
- no accidental reversed support edge;
- later-sibling support of an earlier sibling; and
- fail-closed rejection of a missing prerequisite revision.

Existing runtime/export handoff controls remain in place.

## Remaining correspondence

This PR does not yet reinterpret `buildVerificationRevisionGraph`, whose historical revision-only route still projects `revisionGeneratedFrom`. It also does not construct final `EvidenceEntry` values or change the INT-002 manifest consumer. Those are successor correspondence slices: they must consume the explicit handoff support relation while retaining generation lineage as provenance.

No LLVM behavior or other Phase 1 trusted-computing-base component is changed or audited here.
