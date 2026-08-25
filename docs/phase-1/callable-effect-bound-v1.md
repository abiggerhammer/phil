# Phase 1 callable public effect bound v1

Status: implementation note for the CALL-011 tranche.

This slice completes the implementation side of `PHIL-CALL-EFFECT-001` by checking one callable implementation's inferred reachable semantic effects against its stabilized public may-effect bound.

## Governing rule

A callable implementation may be narrower than its public effect bound, but it may not exercise an undeclared wider effect.

The checker therefore keeps two sets distinct:

- the exact semantic effects reached by the checked implementation body; and
- the exact public may-effect upper bound carried by the callable contract.

A narrower body does not silently narrow the public interface. A wider body does not silently widen it.

## Checking relation

`checkCallableEffectBound` accepts when the inferred implementation footprint is a subset of the public bound.

On success, `CheckedCallableEffects` records:

- the exact callable `InterfaceRevision`;
- the exact inferred implementation effect set; and
- the unchanged public may-effect bound.

On failure, `CallableEffectBoundExceeded` reports the exact undeclared effect delta together with the public bound and governing interface revision.

## Higher-order interaction

This relation composes directly with the CALL-004/005 effect inference landed earlier:

- possessing, passing, storing, or returning an effectful callable does not itself widen the enclosing implementation footprint;
- a reachable invocation contributes the invoked callable's exact public effect bound; and
- the enclosing callable must still contain that resulting footprint within its own stabilized public effect bound.

Thus a pure higher-order body may possess an effectful callable without becoming effectful, while actually invoking that callable may cause the enclosing public-bound check to reject.

## Conformance

`test/Phase1CallableEffectBoundMain.hs` covers CALL-011, including exact, narrower, and empty implementations; undeclared wider effects; exact undeclared-delta diagnostics; public-bound stability; canonical effect ordering; possession-only higher-order use; and reachable higher-order invocation that exceeds an enclosing bound.

The harness runs as another named step inside the shared Haskell `build-and-test` CI job.

## Still deferred

This slice does not claim scoped-loan closure escape, higher-order callable refinement across authority/failure/resource dimensions, recursive callable checking, provider/foreign qualification, target closure conversion, final source syntax, or the Rocq proof for `PHIL-CALL-EFFECT-001`.
