# Phase 1 callable effect implementation refinement v1

This refinement mechanically connects the production callable-effect path to the Certified `PHIL-CALL-EFFECT-001` semantics.

## Certified surface

`proof/Phil/Core/CallableEffects.v` certifies three connected rules:

1. possessing, passing, storing, or returning a callable is invocation-effect neutral;
2. reachable invocation contributes the callable contract's public may-effect bound; and
3. an implementation footprint may be narrower than the stabilized public bound but may not exceed it, with rejection exposing exactly the undeclared effect delta.

The Certified model is extensional: an effect set is a predicate over opaque semantic effect identities.

## Extracted executable seam

`CallableEffectsImplementation.v` exposes only representation-neutral decisions:

- `CallableUseEffectKind` classifies the five higher-order use forms;
- `callableUseEffectKindContributesPublicBound` decides whether that use contributes the public invocation bound;
- `decideCallableEffectBound subsetFact` owns acceptance/rejection once production supplies a native finite-set subset fact; and
- `effectDeltaBit inferredPresent publicPresent` owns the per-effect undeclared-delta predicate.

`proof/Phil/Core/CallableEffectsImplementationExtraction.v` extracts those decisions to `CallableEffectKernel.hs`. The checked-in `src/CallableEffectKernel.hs` must regenerate byte-identically in the dedicated closeout workflow.

Concrete `SemanticEffect` values are `Text`-backed Haskell identities and never cross into Rocq. `Data.Set` membership, union, subset, difference, and canonicalization remain named representation/runtime foundations.

## Proved correspondence

The correspondence proof shows:

- the five-way use classifier agrees exactly with Certified `addCallableUse`;
- if a supplied subset Boolean reflects Certified extensional `effectSubset`, the extracted bound decision accepts exactly the Certified subset cases;
- accepted decisions construct the same interface/inferred/public checked result certified by `checkedEffectBoundAllowed`;
- rejected decisions imply the implementation footprint is not a subset of the public bound; and
- `effectDeltaBit` is exactly Certified `effectDelta`, including its iff characterization as inferred-present/public-absent.

## Production binding

`src/Phil/Core/Callable.hs` now uses the exact extracted kernel as the semantic decision authority while retaining only concrete finite-set representation work:

- `inferReachableCallableEffects` maps each concrete `CallableUse` to the corresponding extracted use kind; the kernel decides whether the public bound contributes, and native `Set.union` materializes that contribution;
- `checkCallableEffectBound` supplies native `Set.isSubsetOf` as the reflected subset fact and follows the extracted accept/reject decision;
- accepted checks preserve the exact existing interface revision, inferred footprint, and public bound;
- rejected checks materialize `Set.difference inferred publicBound`, then validate every effect in the finite `inferred ∪ publicBound` universe against extracted `effectDeltaBit`; and
- any disagreement between native finite-set representation and the extracted semantic predicate fails closed as `CallableEffectKernelBridgeMismatch`.

No effect identity is serialized into Rocq, and no richer target/runtime representation is made part of the theorem. Reachability itself remains a checked upstream fact: this refinement governs the semantics of already-reachable `CallableUse` observations rather than proving control-flow reachability.

## Residual boundary

Rocq extraction/toolchain correctness and the GHC/Haskell runtime remain trusted. Native `SemanticEffect`/`Text` identity, `Data.Set` equality/membership/union/subset/difference/canonicalization, `InterfaceRevision`, and the truth of checked reachability observations remain primitive representation/runtime foundations.

Callable capture mode, lifecycle/resource transitions, scope/recursion, authority/evidence semantics, provider qualification, syntax, closure conversion, and target/runtime effect enforcement remain separate obligations.
