# PHIL-BND-REP-001 production binding

This closeout binds the already-Certified `PHIL-BND-REP-001` boundary
representation semantics to the exact Rocq-extracted kernel staged by #422.

## Exact kernel

Production checks in `src/BoundaryRepresentationKernel.hs` byte-for-byte from
the #422 staging extraction:

`sha256:9f9c6f424ee5bcb570071a2390917024f2adc7996ea807a053becea414b8dcc8`

`phil-core.cabal` is intentionally unchanged. As with the provider-evidence
closeout, the ordinary component build compiles the imported home module; the
dedicated workflow records the unchanged manifest identity alongside the bound
sources.

## Production mapping binding

`src/Phil/Core/BoundaryMapping.hs` remains responsible for concrete Haskell
identity facts and detailed diagnostic reconstruction. It reflects:

- exact `BoundaryRepresentationId` identity;
- exact `GrammarId` identity;
- exact `ValueTypeRevision` identity;
- exact recognized-grammar identity;
- exact recognized source-value `Name` identity; and
- whether mapping competence returned `MappingAccepted`.

The semantic accept/reject choice and its exact precedence now come from
`decideBoundaryMappingByFacts` in the extracted kernel.

On acceptance, the exact representation, grammar, value type, recognized-source
identity, and semantic-target identity are routed through
`planBoundaryCorrespondence` before native `CorrespondenceEvidence`
reconstruction. Transforming mappings therefore retain the Certified distinction
between source and target rather than constructing evidence independently of the
extracted plan.

Concrete expected/actual identifiers and `MappingRejected detail` remain native
because they are diagnostic payloads, not normalized Certified decision atoms.
An impossible cross-constructor state at the native translation seam fails
closed as a boundary-mapping bridge mismatch.

## Production direction binding

`src/Phil/Core/BoundaryDirection.hs` keeps its public native types unchanged. It
maps native `BoundaryDirection` / `BoundaryUse` values into the extracted kernel,
routes the decision through `decideBoundaryUse`, and maps the exact Certified
accepted/rejected result back into the existing public `Either` interface.

No new direction state or error is introduced.

## Residual boundary

The binding does not prove concrete Haskell equality implementations,
parser/recognizer correctness, or the truth/competence of the supplied mapping
disposition. Rocq extraction/toolchain correctness and the GHC/Haskell runtime
remain trusted.

Encoding qualification/canonicality, serialization, ABI/layout/zero-copy
realization, actual wire I/O, and typed protocol progression remain separate
obligations. This closeout does not widen `PHIL-BND-REP-001` into those layers.

## Exact-head verification

The registered boundary-representation workflow runs as **Phase 1 Boundary
Representation Production Binding**. It:

1. recompiles the Certified theorem and implementation correspondence;
2. fresh-extracts `BoundaryRepresentationKernel.hs`, byte-compares it with the
   checked-in production kernel, and asserts SHA-256 `9f9c6f42…`;
3. strict-compiles the exact kernel and both bound production seams under
   `-Wall -Werror`;
4. strict-builds the ordinary Cabal library/test substrate with the unchanged
   manifest;
5. reruns all 14 direct extracted-kernel controls unchanged;
6. reruns the unchanged 13-case BND-004–007 correspondence corpus; and
7. records exact kernel, mapping, direction, unchanged Cabal, harness, corpus,
   proof, and documentation identities in a closeout artifact.

If the exact-head matrix is green, `PHIL-BND-REP-001` can move to
`Discharged / Implementation Refined`.
