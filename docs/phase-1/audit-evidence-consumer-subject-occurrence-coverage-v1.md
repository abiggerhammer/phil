# Phase 1 audit: evidence-consumer subject-occurrence coverage

This defensive proof-correspondence slice continues `D-RES-SUPPORT-01` / `D-RES-TREE-01` after same-event final evidence-use correspondence landed in #1385.

## Boundary

The existing chain now requires every represented actual evidence use to:

- receive complete subject transport or an explicit checked-closed classification; and
- reach an actual final consumer under the same original checking event.

That is still not enough for a fact which refers to more than one logical subject. The consumer-level transport model carries one source/target `SubjectId` pair per consumer. A multi-subject fact can therefore satisfy the existing consumer-level and final-use conditions while an adapter silently omits a second relevant subject occurrence.

This slice makes the occurrence-level completeness condition explicit:

`actual evidence use -> every actual subject occurrence -> represented occurrence -> source/target endpoints -> legal ExportSubject transport`.

## Proof obligations

`EvidenceConsumerSubjectOccurrenceInventoryCoverage` requires every actual subject occurrence of an actual evidence use to appear in the represented occurrence inventory.

`EvidenceConsumerSubjectOccurrenceEndpointCoverage` requires each represented occurrence to have both source and target `SubjectId` endpoints.

`EvidenceConsumerSubjectOccurrenceTransportPreserved` requires those endpoints to satisfy `ExportSubject` under the **same survivor/rebase state** already used by the consumer-level transport model.

`CompleteEvidenceConsumerSubjectOccurrenceCorrespondence` composes occurrence completeness with the already-landed same-event final-use correspondence.

The negative witness deliberately keeps the earlier final-use theorem true while representing only the first of two actual subject occurrences. The second subject is live, but omission from the occurrence inventory causes the new completeness condition to fail. This shows that one legal consumer-level subject pair is not evidence that every subject of a multi-subject use was accounted for.

The positive two-subject witness represents both occurrences and gives each a complete stable endpoint pair. A checked-closed witness remains valid with no subject occurrences at all, preserving the rule that closed facts do not acquire fabricated subject identities.

## Remaining implementation correspondence

This proof does **not** discover Phil's native subject-occurrence inventory. The Haskell adapter remains responsible for faithfully enumerating every relevant subject occurrence of each actual evidence use and for reflecting the correct stable `SubjectId` values into this model. A complete relation over an incomplete native inventory would still be insufficient.

Likewise, the actual-use domain, original/final event maps, and actual final-consumer relation remain concrete correspondence premises from #1385. For residual-free results, approved event origin must still come from the real producer relationship rather than from the mere presence of a caller-supplied `ResidualSpec`.

The implementation-remediation lane owns those native hookups. This PR states only the proof condition that a complete multi-subject inventory must satisfy and does not compete with the current Haskell original-event preservation repair.

## Scope and trust

This PR is proof/docs/workflow only. It does not modify Haskell production code, source admission, resource ownership or loan state, native lowering, LLVM, packaging, provider qualification, or release consumers. LLVM remains inside the Phase 1 trusted computing base and is not audited here.

Direct immutable named-evidence authority, original-event/forest correspondence, selected-consumer endpoint coverage, subject transport, actual-use selection, checked closed-use classification, and same-event final-use correspondence remain separate already-landed obligations and are reused rather than duplicated.
