# Phase 1 callable refinement boundary v1

> **Historical slice note:** This document records the scope and status of one Phase 1 implementation slice when it landed. “Not yet,” “deferred,” and similar status statements below are historical; see the [Phase 1 implementation notes](README.md) for current status ownership.

Status: implementation note for the CALL-012 tranche.

This slice begins `PHIL-CALL-REFINE-001` with the bounded higher-order substitution case from the Callable and Closure Checking Contract.

## Governing rule

Machine signature compatibility is necessary but not sufficient for callable substitution.

An actual callable may be supplied where an expected callable is required only when the checked semantic boundary does not become stronger for the caller or wider in observable behavior.

For this first slice the checker preserves four independently checked dimensions in addition to an opaque checked machine shape:

- caller-supplied authority requirements;
- semantic may-effect bound;
- caller-visible modeled non-success behavior; and
- callee ownership/lifecycle transition.

## Direction of refinement

The relation is asymmetric.

An actual callable may require **less** caller authority, permit **fewer** semantic effects, and expose **fewer** modeled failure possibilities than the expected contract. Those are ordinary safe strengthenings of what the caller receives.

It may not:

- require authority absent from the expected boundary;
- widen the semantic effect bound;
- introduce an extra typed-negative, declared-terminal, or fatal outcome; or
- silently change the callee ownership transition.

The checker reports the exact excess authority/effect/failure set for widening failures.

## Authority

Authority requirements are stable semantic keys, not provider names, ABI symbols, pointers, file descriptors, or runtime handles. This follows ADR-014: authority may flow through checked value/contract relations but may not be invented by higher-order substitution.

This slice does not yet claim full capability possession or attenuation checking; it fixes only the non-widening relation at the callable boundary.

## Callee transition

`PreserveCallee`, `ConsumeCallee`, and `ReplaceCallee` are exact in v1.

A future nontrivial adapter may relate different transitions only through an explicit checked refinement that accounts for the callable resource residue. The initial higher-order checker does not synthesize such adapters implicitly.

## Interface identity

The expected and actual callable may have distinct `InterfaceRevision`s. Revision identity states which contracts are being related; equality of revisions is not the refinement rule.

Conversely, identical machine shape does not establish semantic refinement.

## Conformance

`test/Phase1CallableRefinementMain.hs` covers CALL-012 with:

- exact semantic refinement acceptance across distinct interface revisions;
- stronger caller-authority rejection under identical machine shape;
- wider effect rejection under identical machine shape;
- extra fatal-outcome rejection under identical machine shape;
- incompatible callee-transition rejection;
- acceptance of a semantically narrower actual;
- ordinary machine-shape mismatch rejection; and
- order-independent canonical widening diagnostics.

The harness runs as a named step inside the shared Haskell `build-and-test` CI job.

## Still deferred

This slice does not yet claim the complete `PHIL-CALL-REFINE-001` obligation. In particular it defers:

- dependent parameter/result resource refinement and precondition/postcondition variance;
- named-recursive callable checking through stabilized contracts (`CALL-013`);
- foreign/provider callable qualification (`CALL-015`);
- target closure-conversion preservation (`CALL-016`);
- callable cost refinement;
- assumption/residual-obligation refinement;
- general automatic callable subtyping;
- final callable surface syntax; and
- Rocq proof.
