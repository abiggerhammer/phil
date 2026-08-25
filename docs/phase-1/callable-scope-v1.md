# Phase 1 callable scope boundary v1

Status: implementation note for `PHIL-CALL-SCOPE-001`, covering CALL-010 and CALL-014.

## Governing rule

Phase 1 uses a deliberately bounded closure-scope rule rather than introducing a general escaping-borrow lifetime system.

A closure capture can be structurally valid yet lifetime-invalid. Scope checking is therefore separate from ordinary closure capture ownership and structural-mode checking.

## Scoped shared loans

A scoped shared-loan capture carries an exact `LoanScopeKey`.

- an escaping closure may not capture a scoped shared-loan view;
- a local closure may capture such a view only when the checker can show that the closure is contained in the exact loan validity scope represented by this bounded model;
- a closure claimed to be contained in another scope rejects; and
- scope-independent owned/copied values are unaffected by this lifetime rule.

Exact-scope equality is intentionally conservative. This slice does not define scope nesting, lifetime subtyping, general escaping borrowed closures, or lifetime polymorphism. A future richer lifetime system may admit more programs while preserving the same no-lifetime-extension invariant.

## Restricted recursive closure environments

Phase 1 separately checks the runtime closure-environment reference graph.

Each node records:

- one exact callable ownership occurrence;
- the closure occurrences directly referenced by its environment; and
- the exact affine/linear capture occurrences hidden in that environment.

Unknown references and duplicate closure-node identities fail closed.

Strongly connected closure-environment components are then inspected. An acyclic closure may own restricted captures normally. A recursive cycle with no restricted captures is also admitted. But any closure-environment cycle containing a restricted capture rejects in the Phase 1 fragment, because the cycle would hide that restricted ownership occurrence behind self-reference without an explicit visible resource transition.

This rejection is a bounded Phase 1 design choice, not a claim that resource-carrying recursive closures are impossible in principle. Later language revisions may admit them through explicit consume/successor or other visible resource-state semantics.

Named recursive callables checked through stabilized contracts are not rejected merely for recursion; this rule concerns runtime closure-environment cycles with hidden restricted captures.

## Conformance

`test/Phase1CallableScopeMain.hs` covers:

- CALL-010 escaping scoped-loan rejection;
- same-scope local capture acceptance;
- mismatched-scope rejection;
- scope-independent escaping capture acceptance;
- CALL-014 restricted self-cycle rejection;
- restricted mutual-cycle rejection;
- unrestricted recursive-environment acceptance;
- acyclic restricted-environment acceptance;
- unknown recursive references;
- duplicate recursion-node identities; and
- canonical cycle diagnostics under node-order changes.

The harness runs as a named step inside the shared Haskell `build-and-test` CI job.

## Still deferred

This slice does not claim general lifetime inference, mutable/exclusive borrowing, arbitrary borrowed-closure escape, source closure syntax, higher-order callable refinement, recursive named-callable contract checking, provider/foreign qualification, target closure conversion, or Rocq proof.
