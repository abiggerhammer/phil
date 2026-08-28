# Phase 1 callable scope proof v1

This note records the first Rocq proof authority for `PHIL-CALL-SCOPE-001`, covering the already-implemented CALL-010 and CALL-014 rules without changing production behavior.

## Certified semantic surface

The proof separates the existing bounded Phase 1 rule into two parts.

### Scoped shared-loan capture

`CallableScope.v` models the same three capture outcomes used by production:

- a scope-independent capture is always admitted by this lifetime rule;
- a scoped shared-loan capture in an escaping closure is rejected; and
- a scoped shared-loan capture in a local closure is admitted exactly when the closure's declared containment scope equals the loan validity scope.

The theorem `scope_capture_accept_iff_valid` reflects the executable decision into the declarative validity proposition. Dedicated theorems pin the escaping, exact-scope, mismatched-scope, and scope-independent cases used by CALL-010.

### Restricted recursive closure environments

The proof models a closure-environment graph extensionally:

- nodes have stable occurrence identities;
- references are directed edges;
- a cycle is a non-empty graph path from an occurrence back to itself; and
- a graph is valid only when node identities are unique, all references are known, and no node carrying a restricted capture lies on a cycle.

This yields direct rejection theorems for duplicate identities, unknown references, restricted self-cycles, and restricted mutual cycles. It also proves that an all-unrestricted recursive environment satisfies the cycle rule and that restricted nodes are admissible when they are acyclic.

The graph theorem is intentionally phrased in terms of reachability rather than the implementation's `Data.Graph.stronglyConnComp`. The equivalence between Haskell SCC discovery and this finite graph semantics remains an explicit implementation-correspondence boundary for a later refinement tranche.

## Representation and implementation boundaries

The proof does not identify Rocq naturals with concrete production identities. The following remain explicit correspondence/runtime foundations:

- `CallableOccurrenceKey`, `CaptureOccurrenceKey`, and `LoanScopeKey` Text equality;
- `Data.Map` duplicate/reference validation;
- `Data.Set` canonicalization and diagnostic payload construction;
- `Data.Graph.stronglyConnComp` SCC discovery;
- list traversal and first-error diagnostic order; and
- source-level lifetime/scope inference.

The unchanged `test/Phase1CallableScopeMain.hs` corpus remains the production correspondence harness for these concrete boundaries.

## Scope of the claim

This proof certifies only the bounded Phase 1 no-lifetime-extension and no-hidden-restricted-cycle rule already documented in `callable-scope-v1.md`. It does not claim a general borrow checker, lifetime subtyping, mutable/exclusive loans, arbitrary borrowed closure escape, or that future language revisions cannot admit restricted recursive closures through explicit visible resource transitions.
