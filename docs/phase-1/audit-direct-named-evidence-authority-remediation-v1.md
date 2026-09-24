# Phase 1 audit remediation: direct named-evidence authority

Lineage: `D-CERT-SUPPORT-01`, following the direct named-evidence proof correspondence and the N3 durable logical-subject repairs.

## Problem

`StaticByEvidence Name` records which Core proof binding discharged an obligation, but the display name is not an immutable assurance identity. Before this repair, the checker-to-ledger handoff and INT-002 manifest closure had an exact immutable-support path for certificate `EvidenceFact` assumptions, while a direct named-evidence disposition could reach the handoff without a corresponding `EvidenceEntryId` relation.

That gap matters independently of resource ownership. A later binding may reuse the same spelling, and durable logical typing does not grant evidence identity. The repair therefore does not restore consumed owners, infer authority from equal types, or reject valid direct evidence.

## Exact authority relation

A direct authority registry is keyed by `(ObligationId, Name)`, not by `Name` alone. The obligation key is the concrete checking event that selected the proof. Its immutable `EvidenceEntryId` must resolve through the assurance ledger to a revision whose:

- canonical proposition equals the exact resolved proposition selected by Core;
- semantic subject IDs equal the architecture-owned subject IDs for that checking event; and
- scope equals the Core obligation scope for that checking event.

`attachDirectNamedEvidenceAuthority` adds the selected immutable evidence ID as precise `DependsOnEvidence` support on that direct handoff. It does not alter the live `ResourceContext`, create a replacement proof binding, or reinterpret a same-spelled later value as the original subject.

`handoffResolvedObligationWithAllEvidenceAuthority` composes this direct relation after the existing certificate `EvidenceFact` authority checks. Mixed trees therefore retain both authority disciplines instead of allowing one route to bypass the other.

## Final-consumer correspondence

`bindHandoffDirectEvidence` refuses a raw `StaticByEvidence` handoff that carries no immutable evidence support. For an authority-bound handoff it rebinds the direct consumer evidence record to the exact handoff dependencies and recomputes the digest, mirroring the fixed-point discipline already used for certificate evidence.

`ManifestClosureHandoff` now carries a separate revision-to-evidence map for every direct named-evidence handoff. `closeVerificationBundleWithHandoff` requires its domain to equal the direct handoff domain, requires the mapped evidence to be selected, and requires `bindHandoffDirectEvidence` to be a fixed point before ordinary manifest verification. The ordinary manifest verifier then checks the referenced `DependsOnEvidence` entry as selected immutable support.

Certificate mappings remain separate. No fabricated decision certificate is created for direct evidence, and certificate-only callers provide an empty direct-evidence map.

## Permanent replay

`test/AssuranceDirectNamedEvidenceAuthorityMain.hs` covers:

- valid direct evidence with exact immutable proposition, subject, scope, checking-event identity, and final closure;
- rejection of a raw direct handoff without immutable support;
- rejection when the same display name is registered for another checking event;
- proposition, subject, and scope mismatch rejection;
- final closure requiring every direct handoff to have an exact mapped evidence entry;
- rejection when the direct consumer evidence drops the selected proof dependency; and
- rejection when the final direct mapping points at another evidence revision.

The existing certificate handoff/manifest regression remains unchanged except for the now-explicit empty direct-evidence domain.

## Preserved boundaries

This is a Phase 1 assurance-correspondence repair. It does not change proof-only Rocq work, resource consumption, N3 product definedness, ordinary product equality, refinement truth-at-formation rules, or LLVM/TCB policy. Valid `StaticByEvidence` remains supported when its authority is exact.
