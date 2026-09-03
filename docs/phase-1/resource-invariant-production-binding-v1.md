# PHIL-RES-INVARIANT-001 — production binding closeout

This closeout binds the exact `ResourceInvariantKernel.hs` staged by #595 to the production `Phil.Systems.ControlStateInvariant` acceptance path.

## Exact staged kernel

- staging PR: #595
- exact green staging head: `fdf010f8c4798f8e5185a78f2fdc2dec63ce7b5c`
- staging merge: `bb481b9fe59d8814be3825a4523e963cef085195`
- exact kernel SHA-256: `7e723862de80652cbe34879d857db54874ff45d4d902173db93e0fe772065079`

`generated/ResourceInvariantKernel.hs` and `src/ResourceInvariantKernel.hs` are byte-identical copies of that extraction.

## Production ownership point

`checkStateBoundaryInvariant` keeps all existing concrete checks and diagnostics. After the real structural state-boundary checker, predecessor-domain checks, exact per-predecessor witness checks, invariant instantiation/focusing, evidence lookup, and decision-certificate establishment have succeeded, the production path derives the four Certified kernel facts:

1. predecessor projection keys are distinct;
2. structural projection was accepted by the real `checkStateBoundaryProjections` call sequenced immediately before the invariant work;
3. every concrete predecessor witness map has exactly the declared state-slot domain;
4. the set of predecessor keys whose exact instantiated invariant was successfully established equals the admitted predecessor set.

The extracted kernel must return `InvariantBoundaryAcceptedDecision`. Any disagreement is an internal fail-closed invariant. Native errors remain authoritative for concrete diagnostic payloads and no predecessor evidence is synthesized or shared across paths.

## Closeout gate

`Phase 1 Resource Invariant Production Binding` requires:

- fresh Rocq 9.2 extraction at the staged SHA;
- byte identity of fresh, generated, and production kernels;
- package-level `-Werror` build;
- strict typechecking of the production invariant path and direct harness;
- all 5 direct Resource Invariant controls through `src/`;
- the unchanged 6-case RES-013 correspondence corpus.

A fully green exact head closes machine implementation refinement for `PHIL-RES-INVARIANT-001`.
