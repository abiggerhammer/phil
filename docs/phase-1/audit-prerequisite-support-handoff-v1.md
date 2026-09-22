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

When `bindHandoffCertificateEvidence` finalizes the entry, exact mapped `EvidenceFact` dependencies are unioned with any already-retained precise `DependsOnEvidence` dependencies, while whole-obligation dependencies are replaced by the authoritative prerequisite relation from the handoff. This preserves #1309's distinction between independently precise evidence-entry support and whole-obligation support. Only the latter is projected into the revision support graph.

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
- preservation of independent precise evidence dependencies while stale whole-obligation dependencies are replaced; and
- preservation of the distinction between precise evidence dependencies and revision-graph support.

Existing runtime/export handoff controls remain in place.

## INT-002 final-consumer correspondence

`closeVerificationBundleWithHandoff` is the INT-002 closure route for bundles produced from these checker handoff records. It takes the complete relevant `LedgerHandoff` set plus an explicit revision-to-evidence-entry binding for every `StaticByCertificate` node and checks the correspondence before ordinary manifest closure:

- every handoff revision must be the exact revision carried by the bundle graph;
- the graph edges whose consumer is a certificate handoff must equal the handoff's explicit prerequisite-support edges, so generation lineage or a parallel dependency reconstruction cannot substitute for certificate support;
- every certificate handoff must name exactly one selected immutable evidence entry;
- reapplying `bindHandoffCertificateEvidence` to that ledger entry must be a fixed point, which requires all handoff `DependsOnEvidence` and `DependsOnObligation` support to be present, rejects stale whole-obligation edges, and requires the rebound digest; and
- the ordinary `closeVerificationBundle` path then independently checks that the selected entry is exactly the bundle-accepted ledger entry and validates its dependencies through `verifyManifest`.

Independent precise evidence dependencies remain permitted because `bindHandoffCertificateEvidence` preserves them. EvidenceFact dependencies do not become revision-graph edges, and `revisionGeneratedFrom` remains provenance only.

The permanent INT-002 correspondence controls include valid mixed EvidenceFact/prerequisite closure, omission of each dependency kind, omission of the graph support edge, missing certificate-to-evidence binding, and binding a certificate revision to evidence for another revision.

This closes the prerequisite-support consumer hookup tracked by this handoff. It does not establish the broader D-CERT-SUPPORT-01 producer-authority questions for arbitrary `EvidenceFact` maps, nor does it change LLVM behavior or any other Phase 1 trusted-computing-base component.
