# Phase 1 authority attenuation v1

This slice advances `PHIL-AUTH-ATTEN-001` and conformance case `AUTH-003` from ADR-014.

## Boundary

The previous authority-possession slice established that authority exists only through an actually possessed semantic capability value. This slice adds the complementary non-widening relation used when that authority crosses an abstraction boundary.

The core rule is:

> A boundary may preserve or explicitly attenuate authority. It may not silently add authority.

Authority visibility is represented by an `AuthoritySurface` containing:

- an exact authority contract key;
- an exact semantic subject; and
- the complete set of authority operations visible through that surface.

Runtime handles, pointer values, backend symbols, provider names, and capability occurrence identity are not part of this visibility relation. Occurrence ownership remains governed by the authority-possession/resource layer.

## Explicit attenuation

Changing from one public authority contract to a narrower contract requires an exact `AuthorityAttenuationWitness` naming:

- the source authority contract;
- the target authority contract;
- the exact semantic subject; and
- the exact operation set exposed by the target contract.

The target operation set must be a subset of the source operation set. The subject must be unchanged.

This witness is a checked semantic relation, not a runtime coercion. It does not by itself construct, duplicate, borrow, move, or consume a capability occurrence. Those resource consequences remain separate and must be checked by the operation that actually creates or transfers an attenuated capability value.

## Generic, callable, provider, and architecture boundaries

`checkAuthorityBoundary` reuses the same rule for:

- generic bindings;
- callable substitution;
- provider replacement;
- architecture boundaries; and
- other explicitly named semantic boundaries.

If the public authority contract is unchanged, its visible operation surface must also remain unchanged.

If the public contract changes, the boundary must carry an explicit checked attenuation witness. A different contract name or nominally similar interface does not establish refinement by itself.

Any target operation absent from the available source surface is a widening error.

## Joins

Authority joins are conservative. The authority visible after reconvergence must be available on every continuing branch; branch-local authority is never unioned.

This prevents cases such as one branch possessing only `read` and another possessing only `write` from yielding `read + write` merely because control flow reconverges.

Contract changes are not performed implicitly at a join. If branches need a common narrower authority contract, they must be explicitly attenuated to that contract before the join.

## Structural mode remains separate

This slice does not change capability structural mode or lifecycle semantics.

Attenuating authority does not imply that a restricted source capability may be copied. Conversely, preserving or narrowing authority does not itself consume a capability. The resource operation that constructs or transfers any derived capability must independently satisfy ordinary unrestricted/affine/linear rules.

## Conformance coverage

The dedicated harness covers:

- explicit read/write/delete → read-only attenuation;
- widening rejection with exact excess authority;
- exact subject preservation;
- witness binding to source contract, target contract, subject, and visible operation set;
- checked narrowing at a generic boundary;
- widening rejection at generic, callable, and provider boundaries;
- rejection of public contract change without explicit attenuation;
- rejection of silently changing the authority surface under the same contract;
- conservative authority join behavior;
- non-union of branch-local authority;
- subject/contract sensitivity at joins;
- exact projection from a possessed capability to its semantic authority surface; and
- canonical set ordering.

## Deferred

This slice does not yet claim:

- construction/resource semantics for derived attenuated capability values;
- closure/provider reachable-authority confinement (`AUTH-004`);
- foreign ambient-authority policy (`AUTH-006`);
- provider-wide qualification;
- Systems/StageContract authority preservation;
- final surface syntax; or
- Rocq proof of `PHIL-AUTH-ATTEN-001`.
