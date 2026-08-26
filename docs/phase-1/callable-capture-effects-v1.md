# Phase 1 callable capture and effect boundary v1

> **Historical slice note:** This document records the scope and status of one Phase 1 implementation slice when it landed. “Not yet,” “deferred,” and similar status statements below are historical; see the [Phase 1 implementation notes](README.md) for current status ownership.

This is the first executable checker-facing substrate for the callable/closure tranche governed by ADR-015 and the Callable and Closure Checking Contract.

It covers conformance cases `CALL-001` through `CALL-005` only.

## Implemented boundary

- callable contracts are static semantic objects distinct from callable values;
- callee transition is represented explicitly, with `PreserveCallee`, `ConsumeCallee`, and `ReplaceCallee` kept distinct even though this tranche exercises only preservation;
- closure captures use stable term-occurrence identities rather than source names, environment slots, or target addresses;
- unrestricted captures may be copied without strengthening closure mode;
- affine and linear captures must move the restricted occurrence into the sealed closure environment;
- moved restricted occurrences are returned explicitly so the enclosing resource checker can remove predecessor ownership;
- one restricted occurrence cannot be captured twice;
- closure minimum structural mode is the least upper bound under `unrestricted < affine < linear`;
- capture enumeration order is nonsemantic;
- callable effect bounds are may-effect upper bounds on invocation;
- possessing, passing, storing, or returning a callable does not propagate its invocation effects;
- a reachable invocation contributes the exact public callable effect bound to the inferred effect footprint; and
- repeated effect contributions canonicalize as set union.

## Deliberately not claimed yet

This slice does not yet claim:

- full callable body checking;
- capture derivation from source free variables;
- stable subject/evidence preservation inside capture environments;
- explicit authority/capability accounting;
- `PreserveCallee` resource-state verification for restricted closure internals;
- one-shot `ConsumeCallee` checking;
- `ReplaceCallee` predecessor/successor checking;
- scoped-loan escape checking;
- public callable effect-bound refinement (`CALL-011`);
- higher-order callable refinement (`CALL-012`);
- recursion (`CALL-013`/`CALL-014`);
- foreign/provider qualification (`CALL-015`);
- closure conversion or target lowering (`CALL-016`);
- final callable/closure surface syntax; or
- a Rocq proof for the callable obligations.

The Phase 1 harness is `test/Phase1CallableCaptureEffectsMain.hs` and runs as a named step inside the shared Haskell `build-and-test` CI job.
