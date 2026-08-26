# Phase 1 provider lifecycle / interruption checking v1

> **Historical slice note:** This document records the scope and status of one Phase 1 implementation slice when it landed. “Not yet,” “deferred,” and similar status statements below are historical; see the [Phase 1 implementation notes](README.md) for current status ownership.

This slice advances `PHIL-PROV-QUAL-001` with conformance case `PROV-008` from the Provider Qualification Checking and Schema Contract.

## Boundary

The preceding provider slices establish:

- exact public operation correspondence and per-operation callable/resource refinement (`PROV-001–005`);
- abstract/concrete provider-state initialization and transition simulation (`PROV-006`); and
- provider-wide history laws such as no-replace (`PROV-007`).

Those facts do **not** by themselves establish lifecycle or crash semantics. A provider may behave correctly on every ordinary return while exposing a forbidden intermediate state, leaking a restricted resource, or changing retry semantics when interrupted.

The core rule in this slice is:

> Normal-return correctness does not qualify a provider whose in-scope interruption behavior crosses the declared observation boundary in a way the provider lifecycle contract forbids.

## Explicit observation boundary

`ProviderLifecycleContract` names one exact `ProviderObservationBoundaryKey`.

This is the boundary at which externally observable lifecycle claims are interpreted. It may represent, for example:

- the client-visible object namespace;
- a committed database view;
- a device-visible state;
- a remote-service API state; or
- another exact semantic observation boundary.

Implementation-internal temporary state is not automatically client-visible. Conversely, an implementation may not silently move the observation boundary inward to make a lifecycle property easier to satisfy.

## Interruption points

Each in-scope interruption point is keyed by:

- one already-qualified public `ProviderOperationKey`; and
- one `ProviderInterruptionPointKey`.

Interruption-point identity is semantic model identity, not a source line, instruction address, backend label, or stack frame.

Examples for a publish operation include:

- after writing temporary bytes but before publication;
- after publication but before returning success; and
- after metadata update but before durability acknowledgement.

## Lifecycle allowances

For every in-scope interruption point, the public lifecycle contract declares the allowed sets of:

- externally observable provider states;
- cleanup/resource residues; and
- retry dispositions.

These dimensions remain separate.

A crash that leaves the right externally visible bytes but leaks a restricted resource is not accepted merely because the state is otherwise legal. Likewise, a state may be legal while a retry promise is not.

## Implementation lifecycle model

`ProviderLifecycleModel` supplies the implementation's modeled reachable observations for every in-scope lifecycle point.

Every observation records:

- the observation boundary at which it is claimed;
- the observable state;
- the cleanup/resource residue; and
- the retry disposition.

The checker requires exact point-domain coverage: every lifecycle point declared by the contract has a modeled implementation entry, and no undeclared point is silently added.

For every modeled observation, each field must lie inside the corresponding public allowance.

## Partial commit pressure case

A BlobProvider-style `installIfAbsent` contract may permit, at an interruption point before publication:

```text
absent
```

and after publication:

```text
complete
```

while forbidding:

```text
partially-committed
```

An implementation that returns only correct success/failure results during ordinary execution still fails lifecycle qualification if an in-scope interruption can expose `partially-committed` at the client-visible object-store boundary.

## Retry semantics

This slice distinguishes bounded retry dispositions:

- retry forbidden;
- retry the same operation; and
- retry from an explicitly named observable state.

This does not attempt to define a universal retry protocol. It merely keeps retry behavior explicit where the provider lifecycle contract makes it qualification-relevant.

## Cleanup/resource semantics

Lifecycle cleanup uses the same `ProviderResourceResidue` vocabulary as ordinary provider outcome qualification.

This lets the checker reject interruption behavior that leaks, duplicates, consumes, returns, or fabricates provider resources differently from the lifecycle contract, without creating a second resource-state system.

## Evidence boundary

This checker validates a supplied lifecycle model. It does **not** infer that the model is complete merely because a finite crash-test corpus passed.

Completeness of interruption-point reachability remains an assurance obligation that may be justified by, for example:

- exhaustive transition exploration;
- model checking;
- proof;
- translation validation;
- runtime/platform contract evidence; or
- another acceptance rule explicitly admitted by provider qualification.

Tests can support only lifecycle claims whose evidence policy allows them.

## Conformance coverage

The dedicated harness covers:

- legal absent/complete interruption observations;
- rejection of a partially committed externally visible state;
- exact observation-boundary checking;
- interruption cleanup/resource residue rejection;
- retry-disposition rejection;
- missing interruption-point coverage;
- unexpected interruption-point rejection;
- rejection of lifecycle points naming unqualified provider operations;
- multiple legal observable crash states; and
- ordering noninterference.

## Deferred

This slice does not yet claim:

- provider/foreign authority confinement (`PROV-009` / `AUTH-006`);
- evidence-producer competence (`PROV-010`);
- proof that one concrete interruption model exhausts every machine/runtime crash point;
- generic qualification evidence/disposition closure;
- contextual qualification admission;
- ArchitectureRealization selection;
- concrete target/ABI/runtime lifecycle preservation;
- final surface syntax; or
- Rocq proof.
