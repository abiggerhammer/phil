# Phase 1 audit: SYS-013 imported assumption-authority proof boundary

Status: defensive audit / proof-correspondence slice for `D-SYS-ASSUMPTION-AUTHORITY-01`, a scoped continuation of `D-CERT-SUPPORT-01`.

## Question

The live audit handoff records a deliberate split at SYS-013. `Phil.Systems.AssumptionDependency` checks the exact stage-local assumption registry, required forward relation, reverse relation, and validity-scope revision. The Certified `SystemsAssumptionDependenciesPreserved` model additionally requires every retained assumption binding to carry accepted `AssumptionAuthority`: identity, digest, manifest selection, verification-context permission, and validity agreement.

The native SYS-013 record stores only `StageAssumptionKey` and `AssumptionValidityScopeRevision`. Its production binding therefore treats `PHIL-ASSURE-ASSUME-001` as an imported predecessor premise rather than pretending that local graph coherence reconstructs authority.

## Proof slice

`proof/Phil/Assurance/SystemsAssumptionAuthorityBoundary.v` makes that remaining correspondence boundary explicit.

The bounded model distinguishes:

- whether a stage assumption is actually required;
- the stage-local scope and local graph-coherence result;
- an explicit architecture-owned mapping to an immutable assumption identity;
- the expected content digest, semantic subject and owner/boundary identity for that required key; and
- the immutable authority record's scope, selection, permission and current-validity facts.

It proves two things that are useful for the implementation follow-through:

1. exact imported authority implies the weaker local stage-binding facts already available from SYS-013; and
2. the converse is false. A permanent witness has a required key, nonempty stage scope, locally coherent dependency graph and successful immutable-ID lookup, yet points at an authority whose scope is a different revision. Local graph coherence therefore cannot justify passing the abstract `authorityAccepted` premise by itself.

A positive witness fixes the scope and preserves digest, subject, boundary, selection, permission and current validity, establishing the exact relation required by the bounded model.

## Native correspondence

This proof intentionally does not enrich the SYS-013 stage representation. The next implementation correspondence remains a bounded adapter/consumer seam that, for each required stage key, binds the exact stage key and scope to the same immutable `Assumption` record already checked by the assurance manifest/context path. That adapter must reject at least absent authority, wrong content identity, wrong subject/boundary identity, wrong scope, unselected authority, unpermitted authority, and stale/current-validity disagreement.

The competent accepting consumer must require that relation before the stage contributes to final assurance. A proof that the generic authority checker is sound is not evidence that a particular stage assumption was checked.

## Boundaries

This slice does not:

- grant truth to caller-supplied assumptions;
- infer authority from equal spelling of a stage key and an assumption ID;
- collapse declared assumptions into `DependsOnEvidence` or `DependsOnObligation`;
- add the richer general Assurance-node integration explicitly deferred beyond the SYS-013 Phase 1 contract;
- change LLVM or any other Phase 1 trusted-computing-base component; or
- claim the live implementation obligation is closed.

It is proof correspondence only. The active Surface Rocq refinement lane is disjoint, and the implementation-remediation lane touches separate Haskell paths.
