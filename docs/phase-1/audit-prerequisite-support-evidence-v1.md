# PHIL-AUD-PREREQUISITE-SUPPORT-001 evidence-entry correspondence

This slice follows #1298, #1300, and #1306. It binds the explicit prerequisite-support relation produced by `Phil.Assurance.Handoff` into the final dependency field of certificate evidence without reinterpreting generation lineage.

## Exact boundary

`bindHandoffCertificateEvidence` accepts one `LedgerHandoff` node and a provisional `EvidenceEntry` for the same obligation revision. It is defined only for `StaticByCertificate` dispositions.

The adapter preserves existing precise `DependsOnEvidence` dependencies, replaces caller-supplied whole-obligation dependencies with the handoff's authoritative `DependsOnObligation` support set, and then recomputes the evidence digest. This keeps two authority relations distinct:

- precise evidence support remains `DependsOnEvidence evidence-id`;
- certificate prerequisite support remains `DependsOnObligation prerequisite-revision`.

`revisionGeneratedFrom` remains child-to-parent provenance only and is not copied, reversed, or consulted when finalizing evidence dependencies.

## Fail-closed behavior

The adapter rejects an evidence entry whose `evidenceObligationRevision` does not equal the handoff revision. It also rejects use on runtime, export, definition-only, or explicit-evidence dispositions rather than silently manufacturing certificate support for a different assurance mechanism.

## Permanent replay

`AssuranceHandoffMain` now checks that:

- a certificate evidence entry receives the exact parent/consumer-to-child prerequisite dependency;
- an existing `DependsOnEvidence` edge survives unchanged;
- a stale caller-supplied `DependsOnObligation` edge is replaced rather than unioned into the authoritative support set;
- the evidence digest is rebound after dependency replacement;
- revision mismatch fails closed; and
- non-certificate dispositions cannot use the certificate-support adapter.

The earlier lineage, graph-direction, sibling-support, missing-prerequisite, runtime, and export controls remain.

## Remaining correspondence

This slice does not claim to translate `EvidenceFact` references into immutable evidence-entry identities, and it does not change INT-002 manifest closure. The manifest verifier already consumes `DependsOnObligation` as an authority relation; the remaining prerequisite-support integration slice is to ensure the actual INT-002 production path selects this finalized certificate evidence rather than constructing an equivalent-looking entry that omits the handoff support.

No LLVM behavior or other Phase 1 trusted-computing-base component is changed or audited here.
