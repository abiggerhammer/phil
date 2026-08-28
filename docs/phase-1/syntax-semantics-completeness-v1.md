# Phase 1 syntax/semantics completeness reconciliation v1

## Purpose

This note records the Phase 1 semantic-to-surface completeness audit. Its question is deliberately directional:

> For every semantic choice that an ordinary Phil source author is permitted to make in Phase 1, is there a canonical Grammar-v1 form that denotes that choice?

The converse is a different obligation: parsing a form does not make it semantically valid. `grammar/phase1-surface.ebnf` remains the concrete-syntax authority; the semantic contracts and checker decide admissibility.

## Completeness boundary

The audit does **not** require every checker datatype, proof artifact, or lowering object to have source syntax. Every audited semantic object is classified into one of four classes:

1. **source choice** — controlled by the Phil source author; Grammar v1 must expose it;
2. **canonical elaboration** — deterministically derived from source/checked context; exposing another spelling would create a false choice;
3. **assurance/build input** — evidence, qualification, policy, or admission supplied through the assurance/build boundary rather than self-asserted by ordinary source;
4. **realization/internal state** — compiler/runtime/checker state or target realization detail that is not source semantics.

A source-choice item with no spelling is a reconciliation defect. A non-source item gets explicit classification instead of fake syntax.

## Confirmed defects repaired by this pass

| Semantic choice already admitted by Phase 1 | Previous surface gap | Grammar-v1 repair |
| --- | --- | --- |
| Type actual for `T : Type` | generic application could not denote every admitted type actual | structured type actuals have direct syntax; name-shaped type actuals use the single `static_reference` parse and are resolved as `Type` by the expected parameter kind |
| Static session actual and abstract `S : Session` use | session parameters could be declared but not used as role-local sessions | structured session actuals have direct syntax; name-shaped session actuals/use sites use the same single `static_reference` parse and are resolved as `Session` by the expected kind |
| Exact specialized static contract identity | several contract-bearing positions accepted only a bare qualified name | contract-bearing positions use `static_reference` |
| Authority requirement | canonical generic requirement kind had no spelling | `authority T;` requirement |
| Boundary-representation requirement | semantic requirement had no dedicated spelling | `boundary representation T;` requirement |
| Representation requirement | semantic requirement had no spelling | `representation P;` requirement |
| Placement requirement | semantic requirement had no spelling | `placement P;` requirement |
| Cost requirement | semantic requirement had no generic requirement spelling | `cost P;` requirement |
| Environmental requirement | semantic requirement had no spelling | `environment P;` requirement |
| Ordinary finite product/tuple type and value | tuple patterns existed, but no tuple type/value construction | `(T, U, ...)` type and `(x, y, ...)` value; `(x)` remains grouping |
| Callable outcome class | `outcomes` collapsed success/typed-negative/terminal/fatal into an unclassified type set | `success T`, `negative T`, `terminal T`, `fatal T` outcome specs |
| Callable residual obligation | callable/checker semantics retained obligations but surface clauses could not state them | `obligation P;` at callable and per-outcome residue boundaries |
| Intentionally stricter callable/closure possession mode | semantic contract permits stricter one-shot/nonduplicable callable mode | `closure mode unrestricted|affine|linear ...` with semantic no-weakening check |
| Join invariant | JoinContract semantics includes invariant, syntax exposed only state telescope | `join state (...) invariant P` |
| Dependent typed loop state | LoopContract state telescope can carry types, syntax exposed only initial values | `loop state (x : T = e, ...)` |
| Standalone typed-negative control | typed-negative rejection exists independently of fatal failure | `reject e` expression; `fail ... on ...` remains fatal/resource-consuming |

The static-actual factoring is deliberately kind-neutral for name-shaped actuals. `Foo`, `Foo[T]`, and similar static references receive one concrete parse; elaboration uses the already-known generic parameter kind to determine whether that reference denotes a type, session, provider/callable/boundary/architecture contract, index/static value, or other admitted static object. Parser alternative order therefore cannot choose semantics.

The earlier reconciliation remains in force for refinement types, explicit transport, finite `in`/`disjoint`, term-level `offer`, branch-sensitive outcome residues, exact replacement callees, and declaration-level structural modes.

## ADR-024 concurrency extension

ADR-024 subsequently added one bounded author-controlled semantic choice after the original reconciliation: **which already-created executable architecture occurrences are activated as members of the root static CSP process network**.

Grammar v1 exposes that choice only as the architecture item:

```phil
process worker_run = worker;
```

The process site is generative process/activation identity; the right-hand side is a `qualified_name` referring to an already-created executable occurrence. It is deliberately not a `static_reference`, because process declaration does not instantiate or clone its target.

Everything else needed to execute that choice is classified rather than surfaced:

- **canonical elaboration:** finite transitive process-population enumeration from the selected root, ProcessKey derivation from the process occurrence site, and the initial process-network bookkeeping implied by explicit architecture bindings;
- **ordinary checked semantics:** process target validity, exactly-once activation, global restricted-ownership partition, exact role/process binding, synchronous rendezvous, message ownership transfer, local/communication partial-order causality, local terminal closure, and whole-program terminal closure;
- **assurance:** any claimed fairness, deadlock freedom, eventual response, deadline, or other liveness property;
- **realization/internal state:** OS thread/task/PID/worker identities, scheduling, event loops, queueing/buffering, locks/atomics, IPC/device synchronization, placement, and target execution topology.

There is therefore no Phase 1 term-level `spawn`, `await`, future, race combinator, scheduler directive, lock, or mailbox syntax. Those would represent additional semantic choices, not alternate spellings for ADR-024's static process network.

The process production has a positive and malformed-syntax fixture in the production corpus. The semantic obligations are tracked separately as CONC-001–009 and by the Phase 1 concurrency logic-ledger family; parseability does not claim concurrency checking or realization preservation.

## Source-expressible semantic categories after reconciliation

Grammar v1 now provides a route for the Phase 1 source-level categories exercised by the accepted semantic contracts:

- **declarations and identity-bearing public contracts:** modules/imports, records, sums, aliases, claims, callables, functions, providers/implementations, protocols, capabilities, boundary representations, architectures, components, and program roots;
- **generic/static abstraction:** type/index/session/message/effect/provider/callable/boundary/architecture parameters, kind-neutral name-shaped static references plus structured static actuals, exact static contract references, and the admitted public requirement categories;
- **types/data:** intrinsic and named types, refinements, products, record/sum construction and matching, declaration-level mode strengthening, evidence and dependent indices;
- **callables/resources:** preconditions, consume/borrow/authority/effect contracts, classified outcomes, branch residues, postconditions, residual obligations, assumptions, costs, and callee preserve/consume/replace transitions;
- **authority:** explicit capability contracts and possession modes, architecture origin/grant flow, callable authority requirements, and ordinary value-flow attenuation through checked constructors/callables;
- **protocols:** reusable families, exact static applications, role-local sessions, guarded send/receive/select/offer, recursion/continue, term-level communication actions, and exact specialized boundary/framing references;
- **control/resource state:** conditionals/matches, explicit post-join state and invariant, loops with typed state/invariant, continue/break, scoped borrow, typed-negative reject, and fatal failure;
- **boundary semantics:** boundary declarations, receive/send implementation roles, correspondence, canonicality, failures, laws, recognition/validation/encoding terms, and static specialized contract references;
- **architecture/concurrency:** occurrence creation versus references, explicit static process activation sites, protocol/role/binding edges, authority origins/grants, boundary bindings, entries, assumptions, exported obligations, observables, and constraints.

This is an expressibility statement, not a claim that the current Haskell parser or checker has implemented every production.

## Deliberately non-surface semantic objects

The following are intentionally not ordinary `.phil` author-controlled syntax in Phase 1:

- **canonical elaboration products:** derived structural context zone `mode(T)`, canonical lossless coercions, normalized requirement ordering, declaration/interface/definition revisions, deterministic process-population enumeration/ProcessKey derivation, and deterministic projection/bookkeeping facts;
- **generated occurrence identity:** architecture `InstanceKey`, `ProcessKey`, and similar exact occurrence keys derived from the declared occurrence site rather than hand-picked by source;
- **internal protocol/runtime state:** `PendingRecv` and other split-ingress implementation states, temporary loan tokens, checker residual-context representations, and machine/runtime handles;
- **assurance artifacts:** proof/certificate bytes, generic requirement-discharge records, ProviderQualification claim/evidence/admission objects, assurance-policy decisions, liveness evidence, and exact evidence revision metadata;
- **realization artifacts:** ArchitectureRealization, SystemsArtifact, StageContract, runtime-site identities, target thread/task/PID/worker identities, scheduling/placement/buffering/synchronization choices, target ABI/layout choices, target-introduced effects/carriers, and concrete cost lineage.

Ordinary source may **refer to semantic propositions, requirements, provider implementations, architecture contracts, and source-visible target-independent constraints** that those artifacts later justify. It may not self-certify its own qualification or choose target realization by masquerading build metadata as source semantics.

Provider qualification is therefore deliberately external to ordinary source syntax. A `.phil` file may declare a provider implementation and the contract it claims to satisfy; the accepted qualification that permits a build to use that implementation is an assurance object produced/checked outside the source author's self-assertion boundary.

## Completeness invariant for later changes

Any Phase 1 semantic extension or reconciliation should answer these questions before landing:

1. Is this object/transition a source-author choice?
2. If yes, what exact Grammar-v1 production denotes it, and what accepted/rejected corpus case protects that production?
3. If no, which of canonical elaboration, assurance/build input, or realization/internal state owns it?
4. Can two semantically distinct source choices collapse to one spelling and thereby erase a competence distinction?
5. Can syntax accidentally create evidence, authority, identity, qualification, or realization choice that belongs to a later competent layer?
6. When one spelling is valid at several static kinds, does it have one concrete parse with expected-kind elaboration rather than several competing parses whose order could choose semantics?

The target property is not constructor-for-constructor syntax coverage. It is **source-semantic surjectivity onto the admitted author-controlled Phase 1 semantics, with explicit competence boundaries for everything else**.

## Parser corpus

`test/fixtures/phase1-surface/manifest.json` binds the repaired and extended productions to positive whole-file examples and syntax-negative counterexamples. Positive fixtures assert only parseability; semantic acceptance remains deferred. The corpus covers the earlier local reconciliation defects, the broader semantic-completeness repairs, and ADR-024's static process activation form.
