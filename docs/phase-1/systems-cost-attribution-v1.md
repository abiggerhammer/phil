# Phase 1 Systems cost attribution v1

Status: bounded executable conformance slice for `SYS-018`.

## Governing rule

The selected compilation profile must expose an exact cost graph for every modeled runtime, transfer, checking, and target-staging mechanism that remains physically relevant.

> Semantic claims may reference costs, but they do not own them. Distinct semantic occurrences retain distinct contribution identities; compatible contributions may aggregate into one final physical/accounting charge only through an explicit relation, and a shared physical mechanism is charged once rather than once per claim.

This extends the identity discipline established by SYS-015 through SYS-017. Cost is neither claim identity nor runtime-site identity nor primitive/profile identity.

## Contribution identity versus final charge identity

SYS-015 introduced one `PhysicalRuntimeCostIdentity` per exact runtime-site occurrence. SYS-017 introduced one `StagingCostIdentity` per selected target staging event. SYS-018 preserves both as **cost contributions**:

```text
CostContributionIdentity =
    RuntimeCostContribution(PhysicalRuntimeCostIdentity)
  | StagingCostContribution(StagingCostIdentity)
```

A contribution records its exact mechanism, ADR-011 cost class, cost shape, and the runtime claims attached to the source site when applicable.

A separate `CostChargeIdentity` names a final physical/accounting line item. Several contributions may map to one charge only when their `CostClass` and complete `CostShape` agree exactly. The final charge retains the complete set of contributing identities and the union of their runtime-claim references.

This distinction is what permits honest aggregation without semantic collapse.

## Runtime profile cost basis

The current Systems IR carries reusable runtime primitive/profile tokens but deliberately does not infer cost semantics from their spelling. SYS-018 therefore accepts selected-profile data:

```text
RuntimeCostBasis {
    primitive_profile
    exact_lowering_decision
    final_charge_identity
}
```

The profile domain must equal the exact set of runtime primitive/profiles present in the verified SYS-016 graph. The referenced lowering decision must exist in the exact predecessor lowering ledger, carry an ADR-011 cost class, and have a nonempty cost shape.

Every exact runtime site then contributes its site-owned physical identity with the class and shape supplied by that selected lowering decision.

## Staging cost basis

SYS-017 already requires every selected staging event to carry an exact `TargetRequired` cost account. SYS-018 imports that event-owned cost unchanged as one staging contribution and assigns it a deterministic final charge identity derived from the staging cost identity.

SYS-018 does not weaken SYS-017's staging requirements; its predecessor verifier runs first.

## Exact attribution relations

The StageContract layer materializes and checks all of the following:

```text
runtime profile -> lowering decision + final charge
runtime site -> site-owned contribution
staging event -> event-owned contribution
contribution -> final charge
runtime claim -> set of final charges
final charge -> exact contributing identities + exact claim union
```

Every relation is independently materialized and compared with a mechanically derived expected relation. Claims can cite a shared final charge repeatedly without creating repeated charge entries.

## Shared mechanism charging

The framed-upload witness supplies a real aggregation case. The Hello and Begin recognition sites are distinct semantic/runtime occurrences, but both select the reusable profile:

```text
upload.runtime.frame_receive
```

Each site keeps its own SYS-015 `PhysicalRuntimeCostIdentity`, so SYS-018 sees two distinct contributions. The selected profile maps both to:

```text
cost.runtime.frame_receive.v1
```

Both contributions use the exact `lower.ingress.frame_storage` ADR-011 cost class and shape, including frequency `per frame`. Because class and shape agree exactly, the two contributions may aggregate into one final charge line item. The charge retains both contribution identities and all associated claims.

If two contributions with different cost classes or different cost shapes are redirected to the same final charge, verification rejects the graph rather than guessing an aggregation rule.

## Other upload charges

The selected upload cost profile binds the remaining runtime profiles to their exact existing lowering decisions:

- `upload.runtime.hello_policy` -> `lower.check.hello_policy`
- `upload.runtime.branch_refinement` -> `lower.check.version_refinement`
- `upload.runtime.begin_policy` -> `lower.check.begin_policy`
- `upload.runtime.receive_exact` -> `lower.check.receive_exact`
- `upload.runtime.send_exact` -> `lower.runtime.send_exact`
- `upload.runtime.digest` -> `lower.runtime.digest`
- `upload.runtime.store` -> `lower.runtime.store`

The digest staging copy contributes its separate SYS-017 target-required cost.

The resulting bounded upload witness has ten exact contributions and nine final charges: aggregation is present and observable, but no semantic occurrence identity disappears.

## Steve

Steve currently has no modeled runtime sites and no selected staging events. It therefore traverses the same SYS-018 schema with empty basis, contribution, charge, and reverse-relation maps. No cost mechanism is invented merely to make the witness nonempty.

## Conformance corpus

The dedicated corpus covers predecessor regression, positive upload and Steve closure, profile coverage, site/event contribution coverage, real compatible aggregation, contribution lineage preservation, claim sharing without duplicated charges, composite-claim attribution, target staging cost, and deterministic identity.

Mutation cases reject profile omission/alias/key drift, unknown or empty-shape lowering decisions, empty final-charge identities, incompatible class/shape aggregation, contribution omission/invention/key drift/class/shape/claim tampering, contribution-to-charge corruption, final-charge omission/invention/identity/lineage tampering, and all runtime-site, runtime-claim, and staging reverse-relation corruption.

## Deferred

SYS-018 does not assign universal numeric performance values. Concrete cost expressions remain selected-profile data. It establishes exact attribution and aggregation structure.

The following remain later work:

- SYS-019 next-stage ABI/deployment requirement export;
- SYS-020 final deterministic Systems/StageContract revision closure;
- proof of the multi-claim/multi-site cost-attribution theorem;
- ADR-017/018 carrier/deployment profile adequacy; and
- benchmark calibration of concrete cost expressions.

SYS-018's invariant is narrower and foundational: every retained physical cost has one explicit accounting home, and semantic multiplicity never silently multiplies physical work.
