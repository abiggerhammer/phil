# Phase 1 callable effect implementation refinement v1

This note stages executable implementation correspondence for `PHIL-CALL-EFFECT-001` without changing production behavior.

## Certified surface

`proof/Phil/Core/CallableEffects.v` already certifies three connected rules:

1. possessing, passing, storing, or returning a callable is invocation-effect neutral;
2. reachable invocation contributes the callable contract's public may-effect bound; and
3. an implementation footprint may be narrower than the stabilized public bound but may not exceed it, with rejection exposing exactly the undeclared effect delta.

The Certified model is extensional: an effect set is a predicate over opaque semantic effect identities.

## Executable seam

`CallableEffectsImplementation.v` extracts only representation-neutral decisions:

- `CallableUseEffectKind` classifies the five higher-order use forms;
- `callableUseEffectKindContributesPublicBound` decides whether that use contributes the public invocation bound;
- `decideCallableEffectBound subsetFact` owns acceptance/rejection once production supplies a native finite-set subset fact; and
- `effectDeltaBit inferredPresent publicPresent` owns the per-effect undeclared-delta predicate.

Concrete `SemanticEffect` values are `Text`-backed Haskell identities and never cross into Rocq. `Data.Set` membership, union, subset, difference, and canonicalization remain named representation/runtime foundations.

## Proved correspondence

The staging proof shows:

- the five-way use classifier agrees exactly with Certified `addCallableUse`;
- if a supplied subset Boolean reflects Certified extensional `effectSubset`, the extracted bound decision accepts exactly the Certified subset cases;
- accepted decisions construct the same interface/inferred/public checked result certified by `checkedEffectBoundAllowed`;
- rejected decisions imply the implementation footprint is not a subset of the public bound; and
- `effectDeltaBit` is exactly Certified `effectDelta`, including its iff characterization as inferred-present/public-absent.

## Production boundary

This staging PR leaves `src/Phil/Core/Callable.hs` unchanged. A later production-binding tranche should:

- route per-use contribution choice through the extracted classifier while retaining native `Set.union`;
- route effect-bound acceptance through the extracted subset decision supplied by `Set.isSubsetOf`;
- preserve the existing exact interface/public/inferred result and diagnostics; and
- fail closed by validating every member of the finite `inferred ∪ public ∪ extra` universe against extracted `effectDeltaBit` before accepting a rejection delta.

Callable capture mode, lifecycle/resource transitions, scope/recursion, authority/evidence semantics, source reachability analysis, provider qualification, syntax, closure conversion, and target/runtime effect enforcement remain separate obligations.
