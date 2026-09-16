# FileSystem production binding v1

This note records the executable production-binding closeout for `PHIL-P1-IO-FS-001`.

## Authoritative extracted kernel

`proof/Phil/Core/FileSystemImplementationExtraction.v` fresh-extracts:

- `decideFileSystemReadByFacts`;
- `decideFileSystemReplaceByFacts`; and
- `replaceShouldInstallBinding`.

The checked-in production kernel is `src/FileSystemKernel.hs`.

Required SHA-256:

`0586a6e10eb8c4e12c2b5b7e80ec228bad911ea8be219ae23ac570948861b645`

CI requires a fresh Rocq extraction to be byte-for-byte identical to the checked-in module and to have exactly this digest.

## Production binding

`src/Phil/IO/FileSystem.hs` computes the concrete native facts already present in the Phase 1 implementation—Path occurrence equality, bound sign, authority-check result, binding presence/content/length, and observed outcome kind—and passes those facts to the extracted kernel.

The kernel owns the ordered admission verdict. Haskell then reconstructs the existing detailed typed diagnostics or checked read/replace values from the same concrete facts. Replace next-state selection is likewise routed through the extracted `replaceShouldInstallBinding` decision.

An impossible native/kernel disagreement fails closed through `FileSystemKernelInvariantViolation`.

## Closeout controls

The production-binding gate must establish all of the following on one exact PR head:

1. the Rocq semantic and implementation proofs compile;
2. a fresh `FileSystemKernel.hs` is extracted;
3. fresh extraction and checked-in kernel are byte-identical;
4. the kernel SHA-256 equals the fixed digest above;
5. direct controls pin all certified read/replace decision priorities and replace state selection;
6. the complete Cabal package builds with `FileSystemKernel` registered as a library module;
7. `Phil.IO.FileSystem` and the unchanged IO-FS pressure corpus pass strict `-Wall -Werror` checks; and
8. the unchanged IO-FS corpus still demonstrates bounded reads, typed negatives, exact namespace authority, process-observable replacement, and failure-state preservation.

Only after the exact-head closeout gate and all attached repository workflows are green may `PHIL-P1-IO-FS-001` move from `Active / Certified` to `Discharged / Implementation Refined`.
