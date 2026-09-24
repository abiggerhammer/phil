# Phase 1 audit: evidence-consumer selection coverage

This defensive proof-correspondence slice continues `D-RES-SUPPORT-01` / `D-RES-TREE-01` after the selected-consumer endpoint-coverage proof.

## Boundary

`EvidenceConsumerEndpointCoverage.v` establishes total subject transport for every consumer already present in the selected subject-bearing domain. The live audit handoff identifies one remaining premise before that result can be credited to the real checker: every actual subject-bearing check/evidence use must be reflected into that selected domain.

This slice makes that premise explicit without changing Phil's implementation or trusted-computing-base boundary.

The required chain is now represented as:

`actual subject-bearing use -> selected consumer -> source and target SubjectId endpoints -> stable subject or checked rebase`.

A concrete Haskell adapter must still enumerate the actual uses faithfully, including every relevant subject occurrence of a multi-subject fact. A genuinely closed fact may remain outside the subject-bearing domain only through a competent checked classification; an omitted or unmapped use is not thereby closed.

## Proof obligations

`EvidenceConsumerSelectionCoverage` requires every actual subject-bearing use to be selected.

`ActualUseCompleteEvidenceConsumerSubjectTransport` requires every actual subject-bearing use to have both subject endpoints and a legal `ExportSubject` relation.

The main composition theorem proves that selection coverage plus the already-landed complete selected-consumer transport yields complete transport for actual uses.

The negative witness deliberately omits an actual consumer from the selected set. The existing selected-domain theorem then holds vacuously, while both selection coverage and actual-use complete transport fail. Positive witnesses retain the stable-subject and checked-rebase cases.

## Scope and trust

This PR is proof/docs/workflow only. It does not modify Haskell production code, source admission, resource ownership, native lowering, LLVM, packaging, provider qualification, or release consumers. LLVM remains inside the Phase 1 trusted computing base and is not audited here.

Exact event-scoped direct named-evidence authority, original-event/forest coverage, endpoint coverage, and subject transport are separate already-landed obligations and are reused rather than duplicated.
