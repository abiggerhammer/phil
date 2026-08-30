# PHIL-ARCH-IMPORT-001 production binding

This closes the bounded implementation-refinement correspondence for the already-Certified architecture/import noninterference obligation.

## Exact extracted kernel

Production checks in `src/ArchitectureImportKernel.hs` byte-for-byte from the extraction staged by #436.

SHA-256:

`91f52bfe9c8990674bbae9324a81a93152cee6ab0907c23d3f9e2a3318b40085`

The kernel owns only:

- selected-export presence;
- local resolution-name freshness; and
- exact construction of the local spelling / `DeclarationIdentity` binding pair.

A module locator is not an argument to the kernel. This preserves the Certified result that moving a module cannot redefine an already-checked declaration identity.

## Production bridge

`src/Phil/Surface/Check.hs` retains the existing public resolver API, concrete `Text` / `Data.Map` representation, module-table traversal, `ImportAll` ordering, and native diagnostics.

The existing two-phase resolver order is unchanged:

1. module and requested-export selection complete first;
2. selected bindings are then inserted into the local resolution scope.

Explicit export selection reflects concrete lookup success into `decideImportResolutionByFacts`, holding the later freshness fact true. Local insertion reflects concrete `Data.Map` freshness into the same extracted decision, holding prior export selection true. This preserves the production list-level precedence while routing both Certified semantic gates through the exact extracted kernel.

Accepted local bindings are reconstructed only through `planImportedBinding`, so the exact local spelling and exact selected `DeclarationIdentity` are preserved.

Impossible disagreement between a literal bridge fact and the extracted decision fails closed through an existing native resolver error rather than accepting a binding.

## Deliberate residual boundary

This refinement does not certify:

- concrete `Text` equality;
- `Data.Map` membership, insertion, traversal, or ordering semantics;
- module-table lookup or export provenance;
- construction or truth of `DeclarationIdentity`;
- package/version solving or repository provenance;
- final Phil import syntax;
- declaration-checking soundness; or
- GHC/Rocq/runtime/toolchain correctness.

Those remain explicit native, evidence, or separate semantic boundaries.

## Closeout criterion

The dedicated workflow fresh-extracts `ArchitectureImportKernel.hs`, byte-compares it with the checked-in production kernel, asserts the harvested SHA-256, strict-compiles the kernel and bound resolver, reruns the unchanged five direct kernel controls and unchanged 10-case ARCH-001 corpus, and records exact-head production-binding identities.

A fully green exact-head matrix is sufficient to promote `PHIL-ARCH-IMPORT-001` from `Discharged / Certified` to `Discharged / Implementation Refined`.
