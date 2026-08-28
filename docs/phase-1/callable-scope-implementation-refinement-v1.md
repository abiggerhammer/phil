# Phase 1 callable scope implementation refinement v1

This note stages executable implementation correspondence for `PHIL-CALL-SCOPE-001` without changing production behavior.

## Certified surface

`proof/Phil/Core/CallableScope.v` certifies the bounded CALL-010/CALL-014 semantics:

- scope-independent closure captures are unaffected by the scoped-loan rule;
- escaping closures may not capture a scoped shared-loan view;
- a contained closure may capture a scoped shared-loan view only when the closure scope exactly equals the loan scope;
- recursive closure nodes must be unique;
- recursive closure references must resolve; and
- no closure occurrence carrying a restricted capture may lie on a non-empty closure-environment reference cycle.

The graph theorem is stated over semantic reachability, not over any particular SCC implementation.

## Executable seam

`CallableScopeImplementation.v` extracts two representation-neutral decisions.

### Scope capture

`decideScopeCaptureByFacts isEscaping isScopedLoan sameScope` owns the final CALL-010 classification:

- independent capture → accepted;
- scoped loan + escaping closure → escaping-loan rejection;
- scoped loan + contained closure + equal scope → accepted; and
- scoped loan + contained closure + unequal scope → outside-validity rejection.

The correspondence theorem proves that the reflected Boolean facts computed from the Certified model produce exactly `decideClosureScopeCapture`.

### Recursive closure graph

`decideRecursiveClosureGraphFacts uniqueNodes referencesKnown noRestrictedCycle` owns the ordered CALL-014 graph classification:

1. duplicate node;
2. unknown reference;
3. restricted recursive cycle; or
4. accepted.

Acceptance is proved equivalent to Certified `recursiveClosureGraphValid` whenever the three Boolean inputs faithfully reflect node uniqueness, reference resolution, and absence of restricted cycles. Separate theorems fix the same first-error precedence used by production.

## Production boundary

The extracted kernel deliberately does not own concrete graph or identity machinery.

Production remains responsible for:

- `CallableOccurrenceKey`, `CaptureOccurrenceKey`, and `LoanScopeKey` equality;
- concrete `Map`/`Set` construction and membership;
- `Data.Graph.stronglyConnComp` and its SCC result;
- deriving the Boolean facts supplied to the extracted decisions;
- concrete diagnostic payloads; and
- source scope/lifetime inference.

A later binding tranche should route final scope-capture and graph acceptance/rejection through the exact extracted kernel, while retaining native graph discovery and failing closed if reflected facts and concrete diagnostic shape disagree.

## Staging gate

`Phase 1 Callable Scope Implementation Refinement`:

- recompiles the Certified CALL-SCOPE model and executable correspondence proof;
- extracts `CallableScopeKernel.hs`;
- typechecks the generated kernel under `-Wall -Werror`;
- typechecks the unchanged `CallableScope.hs` production path; and
- reruns the existing 11-case CALL-010/CALL-014 corpus unchanged.

General lifetime inference/subtyping, mutable/exclusive borrowing, arbitrary borrowed-closure escape, later explicit resource-carrying recursive closures, source syntax, target closure conversion, ABI details, and runtime enforcement remain separate obligations.
