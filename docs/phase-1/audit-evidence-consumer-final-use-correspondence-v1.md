# Phase 1 audit: evidence-consumer final-use correspondence

This defensive proof-correspondence slice continues `D-RES-SUPPORT-01` / `D-RES-TREE-01` after complete actual evidence-use classification landed in #1382.

## Boundary

The existing correspondence chain now accounts for every actual evidence use as either:

- a subject-bearing use with complete selected-consumer endpoint transport; or
- an explicitly checked closed use that does not fabricate subject endpoints.

That is still not enough to justify final evidence credit. The live audit handoff requires the evidence use that reaches the final consuming operation to belong to the **same original checking event**. A correct subject/closed classification can otherwise be reused under another event, and matching event metadata alone is not sufficient if the final consumer never actually uses the evidence.

This slice therefore adds the abstract boundary:

`actual evidence use -> original event -> same-event final evidence use -> actual final consumer use`.

## Proof obligations

`SameEventFinalEvidenceUsePreserved` requires every actual evidence use to have an original event, a final-use event equal to that original event, and a positive final-consumer use record.

`CompleteEvidenceConsumerFinalUseCorrespondence` combines that requirement with the already-landed `CompleteEvidenceConsumerUseCorrespondence` classification/subject-transport result.

The composition theorem keeps the premises separate: complete evidence-use correspondence does not imply same-event final use, and same-event metadata does not imply that a final consumer actually used the evidence.

The witnesses preserve the important distinctions:

- a checked closed use can have complete use correspondence and still fail when its final use is credited to a different event;
- matching event identities still fail when no final use is recorded;
- a genuinely checked closed use can reach the final consumer without fabricated subject endpoints; and
- a stable subject-bearing use can preserve both its subject transport and its original event through final use.

## Remaining implementation correspondence

This proof does **not** claim that Phil's Haskell implementation already reflects every actual check event or final consuming operation into this model. The concrete implementation must bind the real event identity carried by the checker/evidence path to the evidence actually consumed by the final accepting operation.

The implementation-remediation lane may establish that concrete hookup. This proof only states the correspondence condition that the implementation must satisfy; it does not modify or compete with the Haskell final-entry work.

Every relevant subject occurrence of a multi-subject fact must still be represented in the actual subject-bearing inventory. That remains a concrete inventory/reflection premise rather than something inferred from this event-level proof.

## Scope and trust

This PR is proof/docs/workflow only. It does not modify Haskell production code, source admission, resource ownership, native lowering, LLVM, packaging, provider qualification, or release consumers. LLVM remains inside the Phase 1 trusted computing base and is not audited here.

Direct immutable named-evidence authority, original-event/forest correspondence, endpoint coverage, subject transport, actual subject-bearing selection, and checked closed-use classification remain separate already-landed obligations and are reused rather than duplicated.
