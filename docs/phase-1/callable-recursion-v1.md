# Phase 1 named callable recursion boundary v1

Status: implementation note for `CALL-013` / `PHIL-CALL-REFINE-001`.

## Governing rule

Named recursive and mutually recursive callables are checked through stabilized public callable contracts, never through privileged knowledge of the bodies currently being checked.

The recursive hypothesis is therefore a projection:

```text
NamedCallableKey -> CallableRefinementSurface
```

It deliberately excludes current `DefinitionRevision`, body-inferred effects, private implementation facts, backend symbols, code pointers, and other implementation detail.

## Stabilization

The entire recursive group is normalized before body checking. Duplicate stable callable identities reject. Declaration ordering is nonsemantic.

A body may resolve a recursive call only through the exact stabilized callable `InterfaceRevision`. A stale requested revision rejects rather than silently rebinding to a changed public contract.

This applies equally to self-recursion and mutual recursion.

## No implementation peeking

Changing a callable's current definition revision or narrowing its current inferred body effects while leaving the stabilized public contract unchanged does not change the recursive environment.

For example, if the public contract permits effect `{read}` but the current body happens to be effect-free, a recursive caller still reasons against `{read}`. The narrower implementation is not privileged recursive knowledge and does not silently narrow the public recursive hypothesis.

Likewise, a future body-local guarantee or authority fact cannot become available to a recursive caller merely because it is true of the current implementation. Such facts must first become part of the stabilized callable contract under the appropriate public refinement rules.

## Relation to assurance

This recursive checking hypothesis is a source-checking rule, not an assurance theorem about the implementation and not an ADR-010 assumption edge. It permits body checking against already-stabilized contracts without circularly allowing a body to certify itself.

## Conformance

`test/Phase1CallableRecursionMain.hs` covers `CALL-013` with:

- self-recursive lookup through the exact public contract;
- mutually recursive lookup across a stabilized group;
- order-independent normalization;
- definition-revision and current-body-effect noninterference;
- public effect-bound preservation despite a narrower current body;
- stale interface revision rejection;
- unknown target rejection; and
- duplicate stable callable identity rejection.

The harness runs as another named step inside the shared Haskell `build-and-test` CI job.

## Still deferred

This slice does not add general termination/liveness reasoning, recursive closure environments with hidden restricted captures (handled separately by `CALL-014`), pre/postcondition refinement, foreign/provider callable qualification (`CALL-015`), target closure conversion (`CALL-016`), final source syntax, or Rocq proof.