# Phase 1 callable lifecycle implementation refinement v1

This note records executable implementation correspondence for `PHIL-CALL-LIFE-001` and its production binding.

## Certified surface

`proof/Phil/Core/CallableLifecycle.v` certifies exact ownership lifecycle for `PreserveCallee`, `ConsumeCallee`, and `ReplaceCallee`:

- preserve requires the exact restricted-capture residue and no successor, and keeps the predecessor resource state unchanged;
- consume requires empty restricted residue and no successor, then removes the predecessor occurrence; and
- replace requires empty restricted residue plus one fresh, distinct successor with the exact declared interface/state identity, then removes the predecessor and installs the successor.

The Certified model deliberately identifies callable ownership by occurrence rather than public interface identity.

## Executable seam

`CallableLifecycleImplementation.v` extracts ordered decisions over representation-neutral Boolean facts supplied by production:

- `decideCallablePreserve residueMatches successorAbsent`;
- `decideCallableConsume residueEmpty successorAbsent`; and
- `decideCallableReplace residueEmpty successorPresent successorDistinct successorFresh interfaceMatches stateMatches`.

The Replace decision order matches production diagnostics exactly: retained residue, missing successor, predecessor-key reuse, already-available successor, interface mismatch, state mismatch, accepted.

Concrete `CallableOccurrenceKey`, `CaptureOccurrenceKey`, `InterfaceRevision`, and `CallableStateKey` values remain native Haskell identities. `Data.Map` lookup/delete/insert/member and `Data.Set` equality/emptiness remain named representation/runtime foundations.

## Proved correspondence

The proof shows:

- Preserve accepts exactly when reflected residue equality and successor absence establish Certified `preserveTransitionValid`;
- Consume accepts exactly when reflected residue emptiness and successor absence establish Certified `consumeTransitionValid`;
- Replace with a concrete successor accepts exactly when reflected residue emptiness, occurrence distinctness/freshness, interface equality, and state equality establish Certified `replaceTransitionValid`;
- Preserve residue mismatch takes precedence over successor diagnostics;
- Consume retained residue takes precedence over successor diagnostics; and
- Replace retained residue and missing-successor diagnostics have the same precedence as the production checker.

## Production binding

`src/Phil/Core/Callable.hs` now routes all three lifecycle validation paths through the exact extracted `src/CallableLifecycleKernel.hs`.

Production supplies only concrete representation facts:

- exact restricted-residue equality or emptiness;
- successor presence;
- predecessor/successor key distinctness;
- native `Map.member` freshness;
- exact interface equality; and
- exact optional state equality.

The extracted kernel owns acceptance and failure precedence. Existing diagnostics retain their exact payloads. Native `Map` state mutation remains outside the extracted decision: Preserve returns the state unchanged, Consume deletes the predecessor, and Replace deletes the predecessor and inserts the accepted successor. Any impossible mismatch between a kernel decision and the concrete `Maybe` successor shape fails closed as `CallableLifecycleKernelBridgeMismatch`.

The dedicated closeout workflow fresh-extracts the lifecycle kernel and requires byte-for-byte identity with the checked-in kernel, typechecks the exact kernel and production binding under `-Wall -Werror`, reruns the unchanged 13-case CALL-006–009 corpus, and records correspondence hashes for the kernel, bound `Callable.hs`, and production corpus.

Callable mode/effects, recursion/refinement, provider qualification, authority/evidence semantics, source syntax, target closure conversion, ABI details, and runtime enforcement remain separate obligations.
