# Phase 1 audit: evidence-consumer use classification

This defensive proof-correspondence slice continues `D-RES-SUPPORT-01` / `D-RES-TREE-01` after the actual subject-bearing evidence-use selection coverage landed in #1377.

## Boundary

The subject-transport chain intentionally applies only to actual **subject-bearing** evidence uses. A genuinely closed evidence fact does not need a fabricated `SubjectId`, but absence from the subject-bearing domain is not itself evidence that a use is closed.

This slice therefore makes the classification boundary explicit:

`actual evidence use -> subject-bearing use OR checked closed use`.

The two branches are not interchangeable. Checked closed uses must be disjoint from the subject-bearing domain. Subject-bearing uses continue through the already-landed chain:

`actual subject-bearing use -> selected consumer -> source and target SubjectId endpoints -> stable subject or checked rebase`.

## Proof obligations

`EvidenceConsumerUseClassificationCoverage` requires every actual evidence use to be classified as subject-bearing or explicitly checked closed.

`CheckedClosedEvidenceUseDisjointFromSubjectBearing` prevents a subject-bearing use from escaping endpoint and transport checks by also being marked closed.

`CompleteEvidenceConsumerUseCorrespondence` gives every actual evidence use either complete subject transport or explicit checked-closed credit with a proof that it is outside the subject-bearing domain.

The main composition theorem lifts classification coverage, closed-use disjointness, and the already-landed actual subject-bearing transport theorem into complete evidence-use correspondence.

The witnesses preserve the important distinctions:

- an actual use omitted from both domains is rejected;
- a checked closed use is accepted without inventing subject endpoints;
- a stable original subject remains valid;
- a checked rebase remains valid; and
- overlapping closed and subject-bearing classification is rejected.

## Remaining implementation correspondence

This proof does **not** claim that Phil's Haskell implementation already enumerates every evidence use or implements the checked closed-use classifier. The concrete adapter must still derive the complete actual-use inventory from the real checker/evidence path and establish closedness competently rather than inferring it from a missing lookup.

The same final consuming operation must still be bound to the resulting support. That final-use integration remains a separate correspondence boundary and may be completed by the implementation-remediation lane.

## Scope and trust

This PR is proof/docs/workflow only. It does not modify Haskell production code, source admission, resource ownership, native lowering, LLVM, packaging, provider qualification, or release consumers. LLVM remains inside the Phase 1 trusted computing base and is not audited here.

Direct immutable named-evidence authority, original-event/forest correspondence, selected-consumer endpoint coverage, subject transport, and actual subject-bearing selection coverage remain separate already-landed obligations and are reused rather than duplicated.
