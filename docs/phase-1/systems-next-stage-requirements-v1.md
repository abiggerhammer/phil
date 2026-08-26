# Phase 1 Systems next-stage requirements v1

Status: bounded executable conformance slice for `SYS-019`.

## Governing rule

Systems is a competence boundary, not the end of the compiler. Backend or target lowering may need exact facts about ABI mapping, representation, calling convention, runtime primitives, placement, alignment, stack bounds, linker/runtime profiles, device features, or target-side enforcement.

Those requirements may not live only in backend convention.

The bounded SYS-019 rule is:

> Every semantically necessary requirement already visible at the Systems boundary and needed by backend/target lowering is exported as an exact `NextStageRequirement`, with exact Systems provenance, an acceptance rule, and a validity scope. The next stage may satisfy or refine that requirement; it may not invent a necessary precondition that Systems never exposed.

`native ABI`, platform defaults, matching symbols, or compiler folklore are not requirement evidence.

## Relation to SYS-014 and SYS-018

`Phil.Systems.NextStageRequirement` layers directly on the checked SYS-018 cost-attribution stage and runs the SYS-018 verifier first.

SYS-014 established that target strengthening cannot appear silently: exact target preconditions are related to source assurance or explicit derived obligations. SYS-019 carries every such exact target precondition across the next competence boundary.

SYS-018 established exact physical-cost attribution and exact reusable runtime-profile selections. SYS-019 also exports one next-stage requirement for every exact reusable runtime primitive/profile because the backend must provide a concrete ABI/signature/calling-convention/runtime realization for it.

This is intentionally a derived export set, not a handwritten wish list.

## Bounded completeness domain

For this slice the mechanically enumerable next-stage requirement domain is the union of:

1. every exact `TargetPreconditionRef` already present in the SYS-014 target-strengthening registry; and
2. every exact `RuntimePrimitiveProfileRef` already present in the SYS-016 reusable-primitive registry.

The verifier derives this domain from the predecessor stage. Omitting one requirement is a stage-contract failure. Adding a requirement outside that domain is also rejected rather than silently widening the boundary.

Later slices may extend the mechanically enumerable domain with deployment/carrier/device requirements when those semantic categories become executable Phase 1 objects.

## Requirement schema

The executable schema is equivalent to:

```text
NextStageRequirement {
    requirement_revision
    basis
    source_systems_refs[]
    required_fact_or_contract
    acceptance_rule
    validity_scope
}
```

The requirement revision is canonical over every field except itself. The stage revision is canonical over the exact SYS-018 predecessor revision and the unordered set of exact requirements.

## Exact Systems provenance

A target-precondition export retains:

- the exact lowering decision and precondition text;
- exact semantic subjects;
- any exact source-assurance revisions already attached by SYS-014; and
- any exact derived-obligation revision introduced by the strengthening.

A runtime-primitive export retains:

- the exact reusable primitive/profile identity;
- every exact runtime site using that profile; and
- the exact final SYS-018 cost-charge identity for that selected runtime profile.

The provenance deliberately does not use backend addresses, symbols, instruction pointers, or textual similarity as semantic identity.

## Shared primitive requirement

SYS-016 already permits several semantic sites to reuse one physical primitive/profile without merging site identity. SYS-019 therefore exports one requirement per primitive/profile, not one requirement per site.

The requirement still retains the full exact site set.

For the upload witness, Hello and Begin recognition both use `upload.runtime.frame_receive`. SYS-019 exports one frame-receive next-stage requirement whose provenance names both distinct runtime sites. This avoids duplicating the ABI/runtime requirement while preserving semantic occurrence lineage.

## Upload witness

The upload SYS-018 predecessor has eight exact reusable runtime primitive profiles:

- `upload.runtime.frame_receive`
- `upload.runtime.hello_policy`
- `upload.runtime.branch_refinement`
- `upload.runtime.begin_policy`
- `upload.runtime.receive_exact`
- `upload.runtime.send_exact`
- `upload.runtime.digest`
- `upload.runtime.store`

SYS-019 therefore derives exactly eight next-stage requirements. Each requires backend lowering to bind the exact primitive profile to a concrete target ABI/signature/calling-convention/runtime realization at every named site.

No upload target-strengthening requirement is invented because the current bounded upload SYS-014 witness has no target precondition.

## Steve witness

Steve currently has no modeled runtime sites in the SYS-016/SYS-018 runtime-profile graph, so SYS-019 does not invent runtime requirements for it.

It does have the exact SYS-014 host-ABI target precondition:

> `host BlobProvider byte-slice ABI preserves pointer/length pairing and length range`

SYS-019 therefore derives exactly one Steve next-stage requirement. Its provenance retains the exact `lower.steve.host-abi` target-precondition reference, semantic subject `steve.blob.byte-slice`, and derived obligation `obligation.phase1.steve.host-abi.v1`.

This is the direct pressure case for the governing rule: backend lowering may establish that exact ABI fact or retain the exact obligation; it may not replace it with the phrase `native ABI`.

## Conformance corpus

The dedicated 25-case corpus covers:

- SYS-018 predecessor regressions for upload and Steve;
- positive exact closure for both witnesses;
- exact upload and Steve requirement counts;
- shared primitive export with both site identities retained;
- exact Steve host-ABI fact and derived-obligation provenance;
- omitted runtime and target requirements;
- invented requirements;
- map-key and embedded-revision drift;
- missing Systems provenance;
- missing runtime-site, cost-charge, target-precondition, derived-obligation, or semantic-subject provenance;
- empty requirement facts;
- `native ABI` folklore substitution;
- runtime ABI/signature contract drift;
- empty acceptance rules and validity scopes; and
- deterministic stage identity under map enumeration order.

## Deterministic identity

`NextStageRequirementRevision` binds the requirement basis, exact Systems provenance, exact required fact/contract, acceptance rule, and validity scope.

`NextStageRequirementStageRevision` binds the exact SYS-018 stage revision and exact unordered requirement registry. Map/set enumeration order is nonsemantic.

## Deferred

This slice intentionally does not yet implement:

- SYS-020 final Systems/StageContract revision closure;
- ADR-017 carrier adequacy or carrier exports;
- ADR-018 deployment qualification;
- arbitrary device-feature or heterogeneous-target requirements not yet represented by the bounded predecessor schema;
- a universal target ABI taxonomy;
- backend satisfaction/proof objects for every requirement; or
- source syntax for target profiles.

SYS-019 establishes the competence-boundary rule needed before those later layers: if backend correctness depends on a fact, that fact must cross the Systems boundary explicitly rather than surviving as compiler folklore.
