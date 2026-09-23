# Phase 1 audit: SYS-012 authoritative consumer-domain proof boundary

Status: defensive audit / proof-correspondence slice for `D-ERASURE-CONSUMER-DOMAIN-01`, continuing the erasure branch of `D-CERT-SUPPORT-01`.

## Question

`Phil.Systems.EvidenceErasure` verifies every entry supplied in `evidenceErasureStageLaterConsumers`. For each supplied consumer it checks source-fact and subject correspondence and then requires that the consumer neither be the claimed last semantic use nor continue to require the erased representation; when a successor invariant is used, it must be the exact invariant named by the matching erasure justification.

That traversal is intentionally local to the supplied map. The live audit handoff therefore leaves one separate correspondence obligation open: the supplied relation must come from a competent producer that enumerates all relevant actual later consumers and preserves the actual source fact, semantic subject, erased representation, ordering relation and successor relation. A locally coherent map cannot establish its own completeness.

## Proof slice

`proof/Phil/Assurance/SystemsErasureConsumerDomainBoundary.v` makes that producer boundary explicit. It distinguishes:

- the authoritative relevant-consumer domain;
- the consumer domain supplied to SYS-012;
- authoritative versus supplied source-fact identity;
- authoritative versus supplied semantic-subject identity;
- authoritative versus supplied erased-representation identity;
- authoritative versus supplied semantic ordering coordinates;
- authoritative versus supplied successor identity; and
- the existing local closure decision over each supplied consumer.

The proof establishes that an exact authoritative domain, exact per-consumer identity correspondence and successful local closure imply the weaker property already checked by traversing the supplied map.

It also supplies a permanent negative witness with two relevant actual consumers while only the first is supplied. The supplied map passes the local traversal, but the authoritative-domain property fails because the second actual consumer is absent. This is the precise reason local SYS-012 success alone cannot prove consumer-domain completeness.

A positive witness preserves both consumers and all fact, subject, representation, ordering and successor coordinates exactly.

## Native correspondence

The admitted Phase 1 route is a bounded inventory adapter, not arbitrary optimized-IR synthesis. The competent producer must derive the relevant semantic-consumer inventory from the production semantic operation/representation inventory used for the same build, bind each entry to the same source fact and stable semantic subject as the erasure justification, preserve the actual ordering/last-use relation and successor identity, and require SYS-012 to consume that exact produced inventory.

The existing `evidenceErasureStageLaterConsumers` digest participation is useful but not sufficient by itself: canonicalizing a caller-supplied map proves what map was checked, not that the map was complete with respect to the actual semantic consumer domain.

This slice does not claim that the current Haskell stage already has such a mandatory producer binding. It identifies the exact proof-correspondence contract that a later implementation remediation or accepting adapter must enforce.

## Boundaries

This work does not require synthesizing arbitrary consumers from optimized LLVM IR, does not reinterpret `NoLaterConsumerRevision` as a trusted completeness oracle, does not permit removal of runtime checks merely because metadata names an erasure, and does not alter LLVM or any other Phase 1 trusted-computing-base component. It adds no Phase 2 requirement and remains disjoint from the dedicated Surface Rocq refinement and implementation-remediation lanes.
