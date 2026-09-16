# Phase 1 named callable recursion boundary v1

Status: implementation note for `CALL-013` / `PHIL-CALL-REFINE-001`.

## Governing rule

Named recursive and mutually recursive callables are checked through stabilized public callable contracts, never through privileged knowledge of the bodies currently being checked.

The recursive hypothesis is therefore a projection:

```text
NamedCallableKey -> CallableRefinementSurface
```

It deliberately excludes current `DefinitionRevision`, body-inferred effects, private implementation facts, backend symbols, code pointers, and other implementation detail.

## Source declaration gate

Grammar v1 makes recursive intent explicit with the `recursive` marker on a named function declaration:

```phil
recursive fn walk(...) satisfies WalkContract {
    ... walk(...) ...
}
```

The marker is **required**, not advisory. A named function body that directly calls itself does not typecheck when the declaration is plain `fn`. Likewise, mutually recursive definitions must belong to an explicitly identified recursive group whose public callable interfaces are stabilized before any member body is checked; ordinary lexical visibility or source order is not permission to form a recursive cycle.

The source checker must not infer recursive intent after discovering a cycle in implementation bodies. Doing so would make body structure determine whether the recursive checking hypothesis exists and would blur the interface-before-body boundary. An unmarked self-recursive call or unmarked recursive SCC therefore rejects at the source/callable integration boundary instead of being silently upgraded to recursive checking.

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

The Grammar-v1/source integration path must additionally cover the source declaration gate with negative fixtures for:

- an unmarked directly self-recursive `fn`; and
- an unmarked mutually recursive cycle.

Both must reject rather than acquiring recursive competence from their bodies.

The harness runs as another named step inside the shared Haskell `build-and-test` CI job.

## Still deferred

This slice does not add general termination/liveness reasoning, recursive closure environments with hidden restricted captures (handled separately by `CALL-014`), pre/postcondition refinement, foreign/provider callable qualification (`CALL-015`), or target closure conversion (`CALL-016`). Grammar-v1 source syntax is now fixed separately; this note records the semantic/typechecking rule that its `recursive` marker exposes.