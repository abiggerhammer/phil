# Phase 1 Systems target-inserted staging effects v1

Status: bounded executable conformance slice for `SYS-017`.

## Governing rule

A target realization may insert work that the source program did not request explicitly. A staging copy is the canonical example: an ABI, accelerator, digest implementation, transport, or memory domain may require bytes to be copied into a target-specific representation before the next semantic operation can proceed.

That copy is not free implementation trivia.

The bounded SYS-017 rule is:

> If a selected target realization inserts a staging copy, the StageContract must record the exact staging requirement and an exact event that accounts for its realization effect, authority surface, failure surface, semantic-subject transfer, and target-required physical cost. Omitting any one of those consequences rejects the stage.

The target may still choose not to stage. SYS-017 does not require copies where none are needed. It prevents an inserted copy from becoming invisible once the target has selected it.

## Relation to SYS-016

`Phil.Systems.StagingEffect` layers directly over the checked SYS-016 primitive-reuse stage. The SYS-016 verifier runs first.

SYS-016 establishes that implementation coincidence does not collapse runtime-site, claim, semantic-subject, or site-owned physical-cost identity. SYS-017 handles a different target phenomenon: the target introduces an additional physical operation and a new target-side representation.

## Selected requirement versus event

The schema separates the selected target requirement from its realized consequences.

A `StagingRequirement` binds one additional copy to an exact predecessor site, primitive/profile, semantic source subject, and introduced target subject.

A `StagingEvent` records the realization effect, authority account, failure surface, subject transfer, and cost account. These are optional fields in the representation precisely so omission remains mechanically distinguishable from an explicit empty authority set or explicit infallibility claim.

The requirement and event maps have exactly the same key domain. A selected requirement without a corresponding event is a StageContract failure.

## Exact predecessor binding

The verifier requires the source site to exist in the SYS-016 predecessor, the declared primitive/profile to equal the exact profile selected there, and the source subject to be one of that site's exact semantic subjects. Equal-looking implementation machinery is not enough.

## Realization effect

The staging event carries an explicit target-only `SemanticEffect`. It must be present and nonempty. This records a consequence of the selected realization without retroactively widening the source callable/provider effect surface.

## Authority account

The staging event must include an explicit authority account. The set may be empty if a target profile has justified that no semantic authority is required, but the field itself may not be absent. `Just {}` therefore means an explicit no-authority claim; `Nothing` means the target failed to account for authority.

Malformed authority subject or operation identities are rejected.

## Failure surface

Failure behavior is explicit even when the selected target claims the staging operation is infallible. The representation distinguishes `StagingInfallible` from `StagingMayFail { ... }`, and an absent failure field never means infallible. A may-fail declaration must contain at least one nonempty failure identity.

## Semantic-subject transfer

Copying bytes creates a distinct target-side subject. Every staging event therefore records the exact source subject, target subject, and nonempty transfer revision. SYS-017 does not infer proposition-specific evidence transport from byte-copy intent; SYS-011 remains the competence boundary for evidence rebinding.

## Target-required cost

Every staging event has an explicit `StagingCostAccount`. Its class must be `TargetRequired`. For this bounded slice the cost shape must account for at least bytes copied and execution frequency. Other ADR-011 dimensions such as allocation count, peak live memory, synchronization, code size, or branch cost may also be populated.

Distinct staging copies may not reuse one staging cost identity. SYS-018 remains responsible for complete aggregation and shared-mechanism charging.

## Upload witness

The upload witness exercises target pressure between exact payload receive and digest validation. The exact `upload.payload` semantic subject at the `upload.runtime.receive_exact` site is staged into `target.upload.payload.digest-staging` for a selected target requiring contiguous digest input.

The event records effect `target.staging.copy-bytes`, allocate/write authority on `target.staging-buffer`, `allocation-failure`, transfer revision `transfer.target.byte-copy-equality.v1`, one staging-buffer allocation, payload-length peak live memory and bytes copied, and once-per-payload frequency.

This is a target-realization pressure witness, not a claim that every conventional target must stage digest input.

## Steve witness

Steve currently requires no staging copy in this bounded profile. It traverses the same schema with empty requirement/event maps; no target-only work is invented merely to make the second witness nonempty.

## Conformance corpus

The dedicated 29-case corpus covers both SYS-016 predecessor regressions, positive upload and Steve closure, presence of all consequence classes, requirement/event omission and identity drift, source-site/profile/subject errors, omitted or malformed effect/authority/failure/transfer/cost accounts, explicit infallibility, target-required cost classification, byte/frequency accounting, duplicate staging cost identity, and deterministic stage identity.

## Deterministic identity

The SYS-017 stage revision binds the exact SYS-016 stage revision; every selected requirement; exact source site/profile/subject and introduced target subject; realization effect; authority and failure surfaces; subject-transfer revision; and complete staging cost account. Map and set enumeration order is nonsemantic.

## Deferred

This slice intentionally does not yet implement complete ADR-011 cost aggregation and shared-mechanism charging (`SYS-018`), next-stage ABI/deployment requirements (`SYS-019`), final Systems/StageContract revision closure (`SYS-020`), ADR-017 carrier adequacy, target-specific proof that an infallibility claim is true, proposition-specific evidence transfer, or source syntax for target staging policy.

SYS-017 establishes the core realization rule: a backend may insert necessary physical work, but it may not make that work semantically invisible.
