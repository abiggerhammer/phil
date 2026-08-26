# Phase 1 provider-wide laws v1

> **Historical slice note:** This document records the scope and status of one Phase 1 implementation slice when it landed. “Not yet,” “deferred,” and similar status statements below are historical; see the [Phase 1 implementation notes](README.md) for current status ownership.

This slice advances `PHIL-PROV-QUAL-001` with conformance case `PROV-007` from the Provider Qualification Checking and Schema Contract.

## Why this layer exists

Per-operation provider qualification is necessary but not sufficient.

An implementation can satisfy every public operation contract independently while still violating a law about sequences of operations. Examples include:

- no-replace publication;
- read-after-publish consistency;
- monotonicity;
- idempotent retry behavior;
- protocol sequencing; and
- cross-operation ownership invariants.

The core rule is:

> Provider-wide laws are checked over public semantic histories, not inferred from operation signatures or from the fact that each operation refines independently.

## Public semantic events

`ProviderImplementationEvent` names an already-qualified provider operation and one implementation outcome.

Before a provider law sees the event, `checkProviderLawTrace` translates that implementation outcome through the exact operation/outcome correspondence established by `PROV-001–005`.

The law therefore consumes `ProviderPublicEvent` values containing only:

- the exact public `ProviderOperationKey`; and
- the exact public `ProviderOutcomeKey`.

Implementation symbol names, helper-call structure, source names, runtime addresses, and private provider state are absent from the law alphabet.

## Law monitor

`ProviderLaw` is a deterministic monitor with:

- one exact `ProviderLawRevision`;
- one initial law state; and
- an explicit transition map from `(law state, public event)` to the next law state.

A missing transition means the public history violates the law.

The monitor state is logical history state for one provider-wide property. It is intentionally distinct from `ProviderStateRelationRevision` and the abstract/concrete implementation state relation used by `PROV-006`.

For example, a no-replace law may distinguish only:

```text
empty
full
```

while the backing implementation may have many concrete filesystem/database states.

## Cross-operation rejection

The conformance corpus includes an `installIfAbsent` provider where one successful install event is individually legal under the accepted operation qualification.

The sequence:

```text
install -> Installed
install -> Installed
```

fails the provider-wide law on the second event.

This is the important `PROV-007` distinction: neither event is malformed in isolation, but the history is illegal.

Likewise, a `read -> Found` event before publication is rejected even though `Found` is a valid public outcome of the read operation in contexts where an object exists.

## Law evidence versus law semantics

`checkProviderLawTrace` and `checkProviderLawCorpus` define the exact semantic evaluator for provider-law evidence.

They do **not** claim that a finite supplied trace corpus is automatically complete over every reachable provider history.

Qualification evidence must separately justify coverage, for example through:

- exhaustive checked transition exploration;
- model checking;
- a proof over a provider-state relation;
- a theorem/certificate establishing the invariant; or
- another evidence form admitted by the provider-law obligation's acceptance rule.

This prevents a successful test corpus from being promoted silently into a universal law proof.

## Relation to PROV-006

`PROV-006` establishes simulation between implementation state and public provider state transitions.

`PROV-007` establishes history laws that may span multiple operations.

The two layers can support one another, but they remain distinct:

- a provider-state simulation can hold while an additional history law fails;
- a history law can apply to a stateless provider with no interesting implementation state relation; and
- the law monitor reasons only over public semantic events after exact outcome translation.

## Conformance coverage

The dedicated harness covers:

- a valid no-replace/read-after-publish history;
- two individually valid operations whose sequence violates no-replace;
- read-before-publish rejection;
- exact implementation-outcome to public-outcome translation;
- unqualified-operation rejection;
- unmapped implementation-outcome rejection;
- exact violation revision/index/state/event diagnostics;
- empty-history behavior; and
- canonical keyed-corpus ordering.

## Deferred

This slice does not yet claim:

- universal reachability/coverage proof for arbitrary implementations;
- lifecycle/crash/interruption semantics (`PROV-008`);
- provider/foreign authority confinement (`PROV-009` / `AUTH-006`);
- evidence-producer subject competence (`PROV-010`);
- generic qualification evidence/disposition closure;
- ungrounded qualification-cycle checking;
- admission policy;
- ArchitectureRealization selection;
- final source syntax; or
- Rocq proof of the provider-law relation.
