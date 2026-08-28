# Phase 1 callable scope implementation refinement v1

This note records production implementation correspondence for `PHIL-CALL-SCOPE-001`.

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

Production derives only the concrete Boolean facts from `ClosureExtent`, `ClosureScopeCapture`, and native `LoanScopeKey` equality. The exact checked-in `src/CallableScopeKernel.hs` then owns the final acceptance/rejection category. A kernel category incompatible with the concrete capture/extent shape fails closed as `CallableScopeKernelBridgeMismatch`.

### Recursive closure graph

`decideRecursiveClosureGraphFacts uniqueNodes referencesKnown noRestrictedCycle` owns the ordered CALL-014 graph classification:

1. duplicate node;
2. unknown reference;
3. restricted recursive cycle; or
4. accepted.

Production retains native deterministic witness discovery:

- `Map` insertion finds the first duplicate node in input order;
- ascending `Map`/`Set` traversal finds the first unresolved reference; and
- `Data.Graph.stronglyConnComp` discovers SCCs and exact restricted-cycle payloads.

Those concrete facts are supplied to the extracted kernel, which owns the final category. Production reconstructs the existing exact diagnostic only when the kernel selects the matching category; any disagreement fails closed as `CallableScopeKernelBridgeMismatch`.

## Representation boundary

The extracted kernel deliberately does not own:

- `CallableOccurrenceKey`, `CaptureOccurrenceKey`, or `LoanScopeKey` equality;
- concrete `Map`/`Set` construction, ordering, or membership;
- `Data.Graph.stronglyConnComp` or SCC discovery correctness;
- concrete diagnostic payload construction; or
- source scope/lifetime inference.

These remain explicit representation/runtime foundations. In particular, the Rocq reachability theorem does not silently certify Haskell's SCC library.

## Production gate

`Phase 1 Callable Scope Implementation Refinement` now:

- recompiles the Certified CALL-SCOPE model and executable correspondence proof;
- fresh-extracts `CallableScopeKernel.hs`;
- requires byte-for-byte equality between fresh extraction and `src/CallableScopeKernel.hs`;
- typechecks both the generated kernel and bound production path under `-Wall -Werror`;
- reruns the unchanged 11-case CALL-010/CALL-014 production corpus; and
- uploads a production correspondence manifest binding the checked kernel, `CallableScope.hs`, and the corpus.

The staging kernel established by #325 has SHA-256 `efd80bdf5a6e7420840afc0e8f14e028eadc7882da5825fa48f7760f5cab51a5`.

General lifetime inference/subtyping, mutable/exclusive borrowing, arbitrary borrowed-closure escape, later explicit resource-carrying recursive closures, source elaboration, target closure conversion, ABI details, and runtime enforcement remain separate obligations.
