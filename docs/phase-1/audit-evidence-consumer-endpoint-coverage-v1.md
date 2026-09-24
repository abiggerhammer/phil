# Phase 1 audit proof correspondence: evidence-consumer endpoint coverage

Lineage: `D-RES-SUPPORT-01` / `D-RES-TREE-01`, following the evidence-consumer subject-transport proof landed in #1364.

The #1364 relation is a correct pair-preservation theorem: when a selected evidence consumer has both an original logical subject and an actually used target subject, those identities must be connected by `ExportSubject`. The latest independent proof review found a distinct domain-completeness gap: the relation does not require either endpoint lookup to succeed, so a selected subject-bearing consumer with a missing source or target satisfies the pair relation vacuously.

## Proof boundary

`proof/Phil/Assurance/EvidenceConsumerEndpointCoverage.v` leaves the existing pair theorem unchanged and adds two propositions:

- `EvidenceConsumerEndpointCoverage`: every selected subject-bearing consumer has both source and target logical subject identities;
- `CompleteEvidenceConsumerSubjectTransport`: every selected subject-bearing consumer has both identities and those identities satisfy the existing `ExportSubject` relation.

The main theorem establishes the exact factorization:

`CompleteEvidenceConsumerSubjectTransport` iff `EvidenceConsumerEndpointCoverage` and `EvidenceConsumerSubjectTransportPreserved`.

The witnesses preserve the important distinctions from the audit handoff:

- selected consumers with a missing source, missing target, or both missing can satisfy the old pair relation vacuously but fail complete transport;
- the stable-original and checked-rebase positive cases remain complete;
- the unrelated same-spelled replacement remains rejected; and
- an honestly empty subject-bearing selection requires no invented subject identity.

## Domain and implementation correspondence

The selected domain is explicitly the subject-bearing evidence-consumer domain. A genuinely closed fact need not acquire a fabricated logical subject, but the concrete adapter must establish a competent closed-fact classification rather than treating an undifferentiated missing endpoint as closed.

This proof still does not establish that the native adapter enumerates every relevant evidence consumer or every subject occurrence of a multi-subject fact. Concrete Haskell reflection must first account for the complete actual consumer/subject domain, then establish endpoint coverage, then the legal transport relation, and finally bind that support to the same final use. Turning an unmapped endpoint into an unselected consumer would evade rather than satisfy this contract.

This slice is proof/docs/workflow only. It does not modify `Phil.Core.Focusing`, `Phil.Core.Discharge`, residual capture, resource ownership, source admission, native lowering, LLVM, packaging, or any Phase 1 trusted-computing-base boundary. The implementation-remediation lane retains ownership of #1359's live-original continuity work. Original-check-event-to-residual-forest completeness, the direct named-evidence immutable adapter, numeric production adapters, and noncertificate final-scope closeout remain separate successor obligations.
