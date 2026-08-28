# Phase 1 callable lifecycle implementation refinement v1

This note stages executable implementation correspondence for `PHIL-CALL-LIFE-001` without changing production behavior.

## Certified surface

`proof/Phil/Core/CallableLifecycle.v` certifies exact ownership lifecycle for `PreserveCallee`, `ConsumeCallee`, and `ReplaceCallee`:

- preserve requires the exact restricted-capture residue and no successor, and keeps the predecessor resource state unchanged;
- consume requires empty restricted residue and no successor, then removes the predecessor occurrence; and
- replace requires empty restricted residue plus one fresh, distinct successor with the exact declared interface/state identity, then removes the predecessor and installs the successor.

The Certified model deliberately identifies callable ownership by occurrence rather than public interface identity.

## Executable seam

`CallableLifecycleImplementation.v` extracts only ordered decisions over representation-neutral Boolean facts supplied by production:

- `decideCallablePreserve residueMatches successorAbsent`;
- `decideCallableConsume residueEmpty successorAbsent`; and
- `decideCallableReplace residueEmpty successorPresent successorDistinct successorFresh interfaceMatches stateMatches`.

The Replace decision order matches production diagnostics exactly: retained residue, missing successor, predecessor-key reuse, already-available successor, interface mismatch, state mismatch, accepted.

Concrete `CallableOccurrenceKey`, `CaptureOccurrenceKey`, `InterfaceRevision`, and `CallableStateKey` values remain native Haskell identities. `Data.Map` lookup/delete/insert/member and `Data.Set` equality/emptiness remain named representation/runtime foundations.

## Proved correspondence

The staging proof shows:

- Preserve accepts exactly when reflected residue equality and successor absence establish Certified `preserveTransitionValid`;
- Consume accepts exactly when reflected residue emptiness and successor absence establish Certified `consumeTransitionValid`;
- Replace with a concrete successor accepts exactly when reflected residue emptiness, occurrence distinctness/freshness, interface equality, and state equality establish Certified `replaceTransitionValid`;
- Preserve residue mismatch takes precedence over successor diagnostics;
- Consume retained residue takes precedence over successor diagnostics; and
- Replace retained residue and missing-successor diagnostics have the same precedence as the current checker.

The extracted kernel does not perform concrete resource-state mutation. Those `Map` operations remain production representation mechanics whose acceptance path will later be governed by the extracted decision.

## Production boundary

This staging tranche leaves `src/Phil/Core/Callable.hs` unchanged. A later binding tranche should:

- route Preserve and Consume validation through the exact extracted decisions while retaining the current exact diagnostics;
- route Replace validation through the exact six-fact ordered decision;
- keep native `Map` deletion/insertion and `Set` residue representation;
- fail closed if any native branch fact cannot be reflected consistently into the extracted kernel; and
- preserve the existing 13-case CALL-006–009 corpus unchanged.

Callable mode/effects, recursion/refinement, provider qualification, authority/evidence semantics, source syntax, target closure conversion, ABI details, and runtime enforcement remain separate obligations.
