# Phase 1 audit remediation: complete definedness support

Finding lineage: `PHIL-AUD-PREREQUISITE-SUPPORT-001` / `D-CERT-SUPPORT-01`.

This implementation-side repair follows the 23 September definedness-support handoff. The existing assurance handoff correctly retained explicit `PrerequisiteFact` references from checked decision certificates, but that syntactic relation was not complete for every prerequisite used to admit the original goal.

Two real resolver cases expose the gap:

- `(a - b) + b == a` requires the generated `b <= a` prerequisite, but the accepted arithmetic certificate can have an empty linear basis after algebraic cancellation, so no `PrerequisiteFact` occurs in the retained certificate syntax;
- `(a - b) == (a - b)` requires the same prerequisite, but the parent closes as `StaticByDefinition`, so there is no decision certificate at all.

In both cases the generated child obligation was already retained. The defect was loss of the semantic parent-to-prerequisite relation, not loss of the node and not an arithmetic-soundness failure.

## Repair

`Phil.Assurance.Handoff` now records every direct prerequisite in the real `ResolvedObligation` tree as semantic `DependsOnObligation` support at the moment immutable handoff revisions are constructed. Certificate traversal remains as an additional support source so that explicit references to earlier siblings continue to work. Both relations are deduplicated by exact immutable revision identity.

`revisionGeneratedFrom` remains provenance only. The repair does not reverse generation lineage or infer support from naming conventions.

For certificate parents, `bindHandoffCertificateEvidence` already replaces caller-supplied obligation dependencies with the authoritative handoff support before rebinding the evidence digest. The newly retained resolver dependency therefore reaches the immutable certificate evidence even when the certificate basis itself is empty.

`closeVerificationBundleWithHandoff` now compares exact graph support for every handoff consumer that actually carries retained support, while continuing to include every certificate consumer even when its exact support set is empty. This makes a definitionally discharged support-bearing parent visible to the final handoff closure without manufacturing a certificate-evidence requirement for it.

## Permanent replay

`Phase1AuditDefinednessSupportMain` uses the real Core resolver rather than a manufactured `ResolvedObligation` and checks:

- R01: an empty-basis arithmetic certificate retains the runtime-bound subtraction prerequisite;
- R02: a `StaticByDefinition` parent retains the same prerequisite;
- C01: pure arithmetic with no prerequisite does not acquire a spurious dependency;
- C02: the verification graph consumes the exact retained support relation; and
- C03: certificate evidence finalization carries the retained resolver dependency and rebinds its digest.

The dedicated workflow also replays the unchanged `DischargeMain`, `AssuranceHandoffMain`, `AssuranceEvidenceFactHandoffMain`, and `AssuranceHandoffManifestClosureMain` corpora.

## Preservation and assurance boundary

This repair does not reject runtime-conditioned arithmetic, undo definitional equality, reinterpret generation lineage as semantic support, treat declaration of a runtime validator as execution of that validator, or restore consumed resource ownership. Exact `EvidenceFact` mapping remains separate and unchanged.

The change is Haskell implementation/assurance plumbing only. The corresponding Rocq completeness/reflection obligation remains owned by the proof/correspondence lane. Direct `StaticByEvidence` authority binding, normalized pending-map/tree association, O01 durable logical-subject interpretation, native reflection, and Phase 2 work remain separate unless independently promoted by the live audit ledger.
