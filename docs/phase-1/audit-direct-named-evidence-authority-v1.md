# Phase 1 audit proof correspondence: direct named-evidence authority

Lineage: `D-CERT-SUPPORT-01`, following the 23 September prerequisite/support producer review and the check-event prerequisite coverage proof.

The existing `EvidenceFactAuthorityPreserved` relation is intentionally certificate-scoped: it quantifies over `EvidenceFact`s actually named by checked decision certificates. The audit handoff records a separate route, `StaticByEvidence Name`, where the resolver directly selects a named proof and may have no certificate-used `EvidenceFact` at all.

That route needs its own authority connection. Successful name-to-record lookup and final consumer use are not enough by themselves; the immutable evidence record used for the direct disposition must preserve the authoritative proved proposition, semantic subject identity, and scope identity for that selected name.

## Proof boundary

`proof/Phil/Assurance/DirectNamedEvidenceAuthority.v` adds a bounded correspondence model with two deliberately separate domains:

- the existing certificate-fact authority model; and
- direct named-evidence selection and immutable consumer support.

The proof establishes that:

- a selected direct name with preserved authority yields one exact immutable evidence record carrying the same proposition, subjects, and scope into the final consumer;
- certificate-fact authority can hold vacuously while a directly selected named proof reaches a consumer with a mismatched scope, so the certificate theorem does not cover this route; and
- a positive direct-evidence witness with exact proposition/subject/scope identity satisfies the new relation without requiring a decision certificate.

The negative witness is a domain/correspondence counterexample, not a claim that the current Phil implementation admits that exact malformed state through source or release entry points.

## Preserved implementation and TCB boundaries

This slice is proof/docs/workflow only. It does not change `Phil.Core.Discharge`, assurance handoff construction, evidence registries, resource ownership, source admission, native lowering, LLVM, packaging, or any Phase 1 trusted-computing-base boundary.

Concrete Haskell `Name` lookup, construction of the authoritative direct-proof registry, immutable `EvidenceEntryId`/revision identity, source/check-event association, and mandatory final-consumer use remain implementation-correspondence premises. Valid in-scope direct evidence remains permitted; rejecting every `StaticByEvidence` result would not satisfy this proof obligation.

Normalized pending-map/resolved-tree association and durable consumed-subject support remain separate handoff items and are not claimed closed here.
