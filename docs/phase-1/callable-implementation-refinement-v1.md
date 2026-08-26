# Phase 1 implementation refinement: CALL-012 pilot

`PHIL-ASSURE-IMPL-CORR-001` distinguishes ordinary Phil proof certification from mechanical production-implementation refinement.

The first pilot is CALL-012 callable refinement. Existing `PHIL-CALL-REFINE-001` remains a valid formal-model certificate; this tranche mechanically connects its bounded semantic slice to the production `checkCallableRefinement` acceptance path.

## Exact production projection

The executable Rocq model consumes a finite `RefinementProjection`:

- a Boolean fact for exact machine-shape equality;
- paired Boolean incidence vectors for actual/expected caller-authority sets;
- paired incidence vectors for public may-effect sets;
- paired incidence vectors for modeled failure sets;
- a Boolean fact for exact full callee-transition equality.

The full transition equality is deliberately stronger than the earlier proof abstraction. The old CALL-012 Rocq model distinguishes preserve/consume/replace by constructor only; production `ReplaceCallee` equality also compares the exact successor interface revision and optional state key. The implementation-refinement relation therefore strengthens the old abstraction rather than erasing that payload distinction.

Rocq proves that:

1. the executable decision accepts exactly the finite implementation-refinement relation;
2. rejection is exactly non-refinement for that relation;
3. accepted implementation projections refine the already-certified CALL-012 abstraction; and
4. for any finite domain covering the actual set, incidence-vector subset is equivalent to extensional membership-predicate subset.

## Extraction and production binding

Rocq extraction emits `CallableRefinementKernel.hs`. The extraction directives map Rocq `bool` and `list` directly to ordinary Haskell `Bool` and lists, so the production bridge has no second handwritten structural marshalling layer.

The checked-in `src/CallableRefinementKernel.hs` is generated source, not an independently maintained implementation. CI regenerates it from Rocq and requires byte-identical equality before any production correspondence test runs.

Production `checkCallableRefinement` constructs each finite set domain as the ascending list of the concrete `Data.Set` union and invokes the extracted `incidenceVector`. It fail-closes unless the domain and both incidence projections round-trip to the exact concrete sets. The semantic accept/reject result comes only from extracted `decideCallableRefinement`. Handwritten Haskell constructs diagnostic payloads and may veto an inconsistent acceptance, but it cannot turn a kernel rejection into success.

The strengthened transition test includes a same-constructor `ReplaceCallee` case whose successor state payload differs; this exercises the exact production equality that was absent from the original normalized CALL-012 model.

## Remaining trusted base

This pilot does not prove GHC, the Haskell runtime, Rocq extraction itself, or `containers`. `Data.Set` ordering/membership/union/fromList semantics and ordinary derived Haskell equality remain named primitive TCB components for the concrete bridge. The bridge algorithm, finite decision procedure, and their connection to the CALL-012 proposition are mechanized; the extracted kernel is mechanically regenerated and content-bound to the production source tree.

For ledger purposes, CALL-012 reaches `Implementation Refined` only after the exact production-binding head passes the full workflow and its proof/translation artifacts are harvested. The reusable migration pattern is then:

`certified proposition -> executable sound/complete relation -> proved representation bridge -> extracted kernel -> byte-identical regeneration -> production acceptance path`.
