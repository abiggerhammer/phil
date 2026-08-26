# CALL-013 implementation refinement v1

`PHIL-CALL-REC-IMPL-001` is the production-correspondence upgrade for the already-certified `PHIL-CALL-REC-001` / CALL-013 semantic slice.

The extracted kernel is polymorphic in the concrete Haskell definition type. It receives only:

- the definition list;
- a stable-key projection;
- a public-callable-surface projection; and
- exact key equality.

It therefore cannot inspect `DefinitionRevision`, current-body effect summaries, or any other private implementation fact. Stabilization itself is decided by the extracted function, which rejects duplicate stable keys and returns exactly the public `(key, surface)` projection when accepted.

Recursive lookup is also performed by the extracted kernel over the stabilized public environment. The production adapter supplies exact key equality and an exact interface-revision predicate; the kernel decides unknown-target, revision-mismatch, and acceptance outcomes.

Rocq proves:

- successful stabilization returns exactly the public projection;
- successful stabilization implies unique stable keys;
- unique stable keys suffice for successful stabilization;
- extracted lookup acceptance identifies an exact public environment member and requires the supplied revision predicate; and
- these accepted production decisions refine the existing `StabilizationAccepted` and `RecursiveLookup` CALL-013 relations.

Production is now bound to the exact checked-in Rocq extraction in `src/CallableRecursionKernel.hs`. `Phil.Core.CallableRecursion` delegates stabilization and recursive lookup decisions to that kernel, then uses concrete `Data.Map` operations only to store the already-decided public environment and construct diagnostics. The adapter fails closed if the extracted public projection disagrees with the concrete projection, if conversion to `Map` collapses an accepted entry, if a `Map.toAscList` / `Map.fromList` round trip changes the environment, or if a concrete diagnostic disagrees with the kernel decision.

CI regenerates the kernel from `CallableRecursionImplementationExtraction.v` and requires it to be byte-identical to the checked-in module before compiling the production adapter and running the CALL-013 behavior corpus. An exact-head green run therefore closes the mechanical production correspondence required for `Implementation Refined`.

Named primitive TCB after production binding: Rocq/extraction, GHC/runtime, derived Haskell equality for stable keys and interface revisions, and `containers` Map extensional representation used to store the already-decided public environment.
