# D-CERT-SUPPORT-01 EvidenceFact immutable-authority handoff

This implementation-correspondence slice follows the proof boundary landed in #1328. It strengthens the existing `(Name, Int) -> EvidenceEntryId` support handoff without replacing the already-landed prerequisite/evidence transport or INT-002 manifest consumer path.

## Authoritative proposition source

A retained Phil Core `DecisionCertificate` stores the exact `Proposition` beside every `EvidenceFact bindingName factIndex` assumption it uses, including `BasisAssumption` occurrences inside linear certificates. That certificate is the object accepted by `checkDecisionCertificate` during `resolveObligation`, so the handoff does not reconstruct the proposition through a second registry walk.

`Phil.Assurance.EvidenceFactAuthority.handoffResolvedObligationWithEvidenceAuthority` traverses those retained certificates and treats the proposition carried with each used `EvidenceFact` as the checker-side proposition identity for the authority check.

## Architecture semantic identity

Core local evidence names and fact indices are not immutable assurance identities, and Core does not itself assign architecture-level semantic subject IDs. The new `EvidenceFactAuthorityBinding` therefore makes the remaining architecture-owned identity explicit:

- immutable `EvidenceEntryId`;
- canonical semantic subject IDs; and
- canonical scope identity.

For every certificate-used fact, the mapped immutable evidence entry must exist, its target `ObligationRevision` must exist, and that revision must have:

1. `revisionStatement` equal to the canonical rendering of the exact proposition retained in the checked certificate;
2. `revisionSubjectIds` equal to the authority binding's semantic subjects, modulo ordering; and
3. `revisionScope` equal to the authority binding's scope.

Any missing authority binding, missing evidence/revision, proposition drift, subject drift, or scope drift fails closed.

## Reuse of the existing support path

After authority validation succeeds, the implementation projects only the already-authorized `EvidenceEntryId` map into `handoffResolvedObligationWithEvidence`. That existing handoff remains responsible for translating `EvidenceFact` to `DependsOnEvidence`, retaining prerequisite support, and feeding the already-landed INT-002 manifest closure. No parallel evidence-dependency or manifest route is introduced.

The permanent controls cover a successful authoritative handoff and negative proposition, subject, scope, and missing-evidence cases under strict `-Wall -Werror` typechecking.

## Boundary retained

This slice does not grant truth to caller-supplied evidence, does not change resource consumption or evidence lookup in Phil Core, and does not alter LLVM or any other Phase 1 trusted-computing-base component. The architecture remains responsible for supplying the semantic subject/scope authority binding; the immutable ledger revision must then match it exactly before a Core-local fact may be transported as immutable evidence support.
