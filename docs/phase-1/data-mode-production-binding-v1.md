# PHIL-DATA-MODE-001 — production binding closeout

This closeout binds the exact `DataModeKernel.hs` staged by #600 to the production Data Mode paths while preserving concrete source, resource, and diagnostic responsibilities in native Haskell.

## Exact staged kernel

- staging PR: #600
- exact green staging head: `5be66b08c8754e3519e65e1c40d918b8b7f7afad`
- staging merge: `f68b8feda4a0bf1cdd8a07486cdb18d271dcab4e`
- Phase 1 Data Mode Proofs run: `33716079102`
- staging artifact: `9878592341`
- staging artifact digest: `sha256:08a42889493212f1779f141af8d88004eadea0bcdbc112efc094b1ff4b4e3bb7`
- exact kernel SHA-256: `32f459278217bc15a33d02bee48333de51de33be7972816a30d4f2406ba41b40`

`generated/DataModeKernel.hs` and `src/DataModeKernel.hs` are byte-identical copies of that extraction. The closeout workflow freshly extracts the kernel again under Rocq 9.2.0 and refuses any byte drift.

## Production ownership points

`Phil.Core.DataModeKernelBridge` is the only representation bridge between concrete `Phil.Core.Syntax.Mode` and the extracted kernel `Mode`.

`Phil.Core.DataMode` now routes:

1. `modeLub`, record mode derivation, and sum mode derivation through the certified kernel;
2. a fully resolved `StrongestMode` list through the certified generic strongest-mode fold, while concrete parameter names and environment lookup remain native and a missing parameter still fails closed before the fold; and
3. successful concrete restricted-source collection through the certified aggregate-formation decision. The Boolean supplied to the kernel is derived from the actual source names and modes returned by sequential `ResourceContext.useBinding` operations. Duplicate affine/linear occurrences therefore continue to reject natively during the real one-shot consumption path; a successful collection is additionally required to satisfy the certified formation postcondition.

`Phil.Core.NominalDataMode` keeps the existing native diagnostic path for weakening and for missing, unadmitted, or empty strengthening justification. Only after that concrete check succeeds does it supply the kernel with the exact derived mode, declared mode, and a strict-justification Boolean that is true only after a real admitted, nonempty resource/lifecycle justification succeeded. The certified result must agree with the native accepted mode. Any disagreement fails closed as `CertifiedNominalModeKernelDisagreement`.

No kernel fact manufactures source ordering, generic parameter identity, resource ownership, or justification authority. Native errors remain authoritative for concrete diagnostic payloads and ordering.

## Closeout gate

`Phase 1 Data Mode Production Binding` requires:

- fresh Rocq 9.2 extraction and exact SHA-256 verification against the #600 staged kernel;
- byte identity of fresh, generated, and production kernel copies;
- the ordinary package library build with `-Werror` as a regression gate;
- strict `-Wall -Werror` typechecking of the exact kernel, representation bridge, bound Data Mode modules, and production-binding harness;
- the 16 direct kernel controls through `src/DataModeKernel.hs`;
- production-path controls for record/sum derivation, generic resolution, nominal acceptance/diagnostics, and actual restricted-owner formation/rejection; and
- the unchanged DATA-001–003, DATA-009, and DATA-014 correspondence corpus.

A fully green exact head closes machine implementation refinement for `PHIL-DATA-MODE-001` and permits promotion from `Discharged / Certified` to `Discharged / Implementation Refined`.
