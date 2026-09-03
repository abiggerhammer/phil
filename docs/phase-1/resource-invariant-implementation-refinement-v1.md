# PHIL-RES-INVARIANT-001 — implementation refinement staging

This staging slice extracts the representation-neutral decision surface already Certified by `proof/Phil/Core/ResourceInvariant.v`. Production Haskell is unchanged here.

## Exact decision surface

`InvariantBoundarySuccess` is the conjunction of four independently reflected facts:

1. the predecessor list is distinct;
2. every relevant predecessor already satisfies the structural resource projection relation;
3. every predecessor has the exact declared invariant-witness domain; and
4. every predecessor independently establishes its own instantiated invariant.

`decideInvariantBoundaryByFacts` reports the first failed gate in that order and otherwise accepts.

The implementation correspondence proves both directions against the Certified record. In particular, structural compatibility and exact witness domains do not imply logical establishment, and evidence from one path cannot substitute for another path because the final establishment fact quantifies over every relevant predecessor.

## Concrete/native boundaries

This extracted kernel does **not** duplicate the production representation work already performed by `Phil.Systems.ControlStateInvariant` and its predecessors:

- `checkStateBoundaryProjections` remains the concrete owner of CFG/state-boundary and resource projection validation, including the already-bound Resource Join/Scope/Loop surfaces;
- binder-domain equality and duplicate-binder diagnostics remain native;
- exact predecessor-domain and predecessor-key diagnostics remain native;
- witness-value equality against each structural state-slot binding remains native and is a concrete strengthening of the theorem's abstract witness-domain relation;
- invariant instantiation, focusing, evidence lookup, decision-certificate proposal/checking, and exact diagnostic payloads remain native mechanisms;
- `PHIL-RES-OBL-001` remains an independent predecessor guarantee and is not duplicated in this kernel.

A later production-binding closeout must derive all four Booleans from those actual successful checks. It must not treat successful structural projection as invariant evidence, and it must not collapse per-predecessor establishment into one global proof bit without demonstrating that every predecessor was checked.

## Staging controls

The staging workflow runs five direct constructor controls covering acceptance and each failure class, then reruns the unchanged six-case RES-013 conformance corpus in `test/Phase1JoinLoopInvariantMain.hs`.

A green staging merge leaves `PHIL-RES-INVARIANT-001` at `Discharged / Certified`. Only a separate exact-kernel production binding may promote it to `Discharged / Implementation Refined`.
