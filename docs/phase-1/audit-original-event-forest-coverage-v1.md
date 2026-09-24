# Phase 1 audit: original check-event to residual-forest coverage

Status: focused defensive proof-correspondence successor after selected evidence-consumer endpoint coverage. This continues the open original-event/forest closeout from `PHIL-AUDIT-20260923-CHECK-EVENT-SCOPE-CALLERS`; it does not introduce a new canonical implementation finding.

## Audit boundary

`CheckEventPrerequisiteCoverage.v` establishes the event-domain side of the chain: once every mandatory prerequisite of an admitted check event is accounted for by certificate or explicit operation support, every such prerequisite reaches the final support relation.

The live audit handoff leaves one distinct completeness step open. A correct support relation is not itself evidence that the actual retained residual forest contains that relation, and a correct retained forest is not itself evidence that the final scope/closure consumer uses it. Reconstructing a smaller inventory from normalized pending entries can therefore make the preceding support theorem true while losing an original condition before final closeout.

## Proof slice

`proof/Phil/Assurance/OriginalEventForestCoverage.v` models the two remaining transports explicitly:

1. **support-to-forest faithful reflection** — every support edge associated with the exact event is retained under that event's residual-forest root; and
2. **forest-to-scope consumption** — every retained prerequisite is consumed by the event's selected final scope relation.

`OriginalEventFinalScopeComplete` then states the end-to-end completeness claim: every mandatory prerequisite of the original check event is present in the final scope relation.

The central theorem composes those two transports with the existing `EventSupportPreserved` result. A second theorem composes the entire prior chain — certificate support, explicit operation support, complete event-domain accounting, faithful forest reflection, and final-scope consumption — into original-event final-scope completeness.

## Negative and positive witnesses

The negative witness reuses the routed definition-only event from `CheckEventPrerequisiteCoverage.v`. Its event support is complete, but a deliberately dropping forest adapter retains nothing. The earlier theorem therefore remains true while final-scope completeness fails. This demonstrates why the support theorem cannot close the original-event/forest handoff by itself.

The positive witness retains the same support relation in the forest and passes that retained relation to the final scope. It establishes the bounded completeness shape without pretending to prove concrete root/scope identity authority or the production adapter.

## Native correspondence still open

This is proof/docs/workflow only. It does not identify or modify the approved Haskell Phase 1 accepting entry. The implementation correspondence must still show that the concrete accepting route:

- derives the mandatory original-event domain from the actual checked result rather than a reconstructed pending-map subset;
- binds the exact original goal/type, logical subject or occurrence, requirement identity, origin, scope, required point and immutable revisions;
- reflects the actual event support into the retained residual forest without dropping definitionally simplified or certificate-free prerequisites;
- feeds that retained relation to the actual local/conditional/export scope consumer; and
- preserves the already-supported stronger-static-discharge and legitimate export cases rather than requiring byte-identical disposition tags.

Direct `StaticByEvidence` native mapping, exact root/scope identity authority, numeric production adapters, and the concrete accepting-entry implementation remain separate correspondence obligations. Existing `ValidityScope`, direct named-evidence authority, subject-transport and endpoint-coverage proofs remain complementary boundaries; this slice does not duplicate or weaken them.

## Phase 1 boundary

No Haskell production code, resource ownership/loan state, residual interpretation, source admission, native lowering, LLVM, release packaging, or trusted-computing-base boundary changes are included. LLVM and other Phase 1 trusted components remain trusted as specified by the frozen charter.
