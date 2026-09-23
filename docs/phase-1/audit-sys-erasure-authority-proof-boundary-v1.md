# Phase 1 audit: SYS-012 imported erasure-authority proof boundary

Status: defensive audit / proof-correspondence slice for `D-ERASURE-PREDECESSOR-BIND-01`, a scoped continuation of `D-CERT-SUPPORT-01`.

## Question

The live audit ledger keeps a deliberate boundary around SYS-012. `Phil.Systems.EvidenceErasure` checks the local erasure justification: the source fact and discharge evidence must bind the exact semantic subject, the representation and last-use coordinates must be present, and all supplied later consumers must be closed over the erased representation or the exact successor invariant. The Certified proof chain additionally requires `PHIL-ASSURE-USE-001`: an independently accepted, selected, certification-scoped, usable immutable Assurance evidence witness for the erasure revision.

The native SYS-012 record does not itself reconstruct that full immutable Assurance authority. Local source/discharge correspondence plus consumer closure therefore cannot justify the imported predecessor premise by itself.

## Proof slice

`proof/Phil/Assurance/SystemsErasureAuthorityBoundary.v` models the remaining imported-authority relation per required erasure justification. It distinguishes:

- the exact erasure-stage revision;
- the exact semantic subject shared by the source fact and discharge evidence;
- an explicit mapping to immutable evidence;
- the immutable evidence revision and subject; and
- manifest selection, certification-scope membership, accepted-revision status, and usability.

The proof establishes that exact imported authority implies the weaker local erasure binding already available from SYS-012. It also provides a permanent negative witness in which the local stage data is coherent and the immutable-evidence lookup succeeds, but the stage names revision `300` while the mapped immutable evidence names revision `301`. The weaker local relation therefore holds while imported authority does not.

A positive witness preserves revision and subject and requires the mapped evidence to be selected, certification-scoped, accepted, and usable.

## Native correspondence

The intended implementation correspondence is a bounded accepting adapter: for each SYS-012 erasure justification that contributes to final assurance, bind its exact discharge/source subject and exact erasure revision to the same immutable Assurance evidence entry already checked by the assurance verifier. That binding must be required before the stage can discharge the imported `PHIL-ASSURE-USE-001` predecessor.

This proof does not claim that the current Haskell SYS-012 representation already performs that adapter step. It also does not replace or close `D-ERASURE-CONSUMER-DOMAIN-01`; completeness of the actual later-consumer/site inventory remains a separate obligation.

## Boundaries

This slice does not grant truth to caller-supplied evidence, infer immutable authority from an equal textual reference, restore consumed resources, add a richer Phase 2 assurance representation, or alter LLVM or any other Phase 1 trusted-computing-base component. It is proof correspondence only and remains disjoint from the dedicated Surface Rocq refinement and implementation-remediation lanes.
