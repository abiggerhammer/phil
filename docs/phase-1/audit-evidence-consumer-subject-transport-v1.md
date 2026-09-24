# Phase 1 audit proof correspondence: evidence-consumer subject transport

Lineage: `D-RES-SUPPORT-01` / `D-RES-TREE-01`, following the durable residual-subject repair review and the direct named-evidence authority proof.

The durable residual-subject work preserves enough logical typing information to interpret an emitted obligation after the affine/linear owner has been consumed. The latest audit handoff separates that typing support from evidence authority: a later binding with the same source spelling can currently be considered as evidence for an older residual unless the implementation also preserves or checks the old logical subject identity.

`Phil.Surface.BranchEvidenceSupport` already gives the proof side the right primitive: stable logical `SubjectId` values plus explicit checked rebases. This slice applies that primitive to evidence consumers.

## Proof boundary

`proof/Phil/Assurance/EvidenceConsumerSubjectTransport.v` models, for each selected evidence consumer:

- the original logical subject that the old obligation/evidence fact denotes;
- the subject actually used by the later evidence consumer;
- the surviving logical-subject set; and
- the explicitly checked rebase relation.

The correspondence requirement is `ExportSubject`: the original subject must either survive unchanged or move through a checked rebase to a surviving target. Source spelling is intentionally absent from the model.

The proof establishes three focused cases:

- a same-spelled replacement with a different logical subject and no checked rebase cannot satisfy the evidence-consumer transport relation;
- a stable original subject can continue to support the evidence consumer unchanged; and
- a distinct surviving target can support the consumer when an explicit checked rebase connects the old subject to that target.

This gives the implementation lane a precise proof-side contract for both direct `StaticByEvidence` uses and solver/certificate evidence assumptions: durable type interpretation does not become evidence identity by itself.

## Preserved implementation and TCB boundaries

This slice is proof/docs/workflow only. It does not modify `Phil.Core.Focusing`, `Phil.Core.Discharge`, residual capture, ownership/loan state, assurance handoff construction, source admission, native lowering, LLVM, packaging, or any Phase 1 trusted-computing-base boundary.

Concrete Haskell reflection remains an implementation-correspondence premise: an actual residual/check event and each actual evidence consumer must be associated with stable logical subject IDs, and any allowed rebase must be checked rather than inferred from `Name` equality or proposition text. The proof does not prescribe a particular stable-ID representation and does not claim that PR #1359 already establishes these premises.

The original-check-event-to-resolved-forest association and the separate noncertificate final-scope closeout remain uncovered successors and are not claimed closed here.
