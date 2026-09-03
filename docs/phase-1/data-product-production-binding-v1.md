# PHIL-DATA-PRODUCT-001 — production binding

This closeout binds the exact executable kernel staged in #615 to the existing DATA-015 finite-product implementation.

## Exact staged identity

- staging PR: #615
- repaired exact green staging head: `6b167a178d4774272b198e3fabf8bdf739adc5de`
- staging merge: `1c1c4b2828e5702ca53ffc562c8171b48b8d7e11`
- dedicated run: `33730439401`
- staging artifact: `9883664616`
- artifact digest: `sha256:5a571c9e541d0e51dc5a98e8c3ae4545866b4e01422e80005b7eb86531865d83`
- exact `DataProductKernel.hs` SHA-256: `d3b7c219a49b2efe622c04a4f9407f108fbc0b7ddf1524cd297be39259f80ed6`

`generated/DataProductKernel.hs` and `src/DataProductKernel.hs` are byte-identical copies of that artifact. CI freshly extracts the kernel and requires the same SHA-256 plus byte equality against both checked-in copies.

## Production ownership split

`PHIL-DATA-MODE-001` already owns product structural-mode folding and restricted-source formation uniqueness. This closeout does not duplicate those decisions.

`Phil.Core.DataMode.eliminateProductBinding` remains the concrete ownership operation. It still performs native product-type recognition, derived-mode agreement, `ResourceContext.useBinding`, and exact successor insertion. Existing native diagnostics remain authoritative.

The new `Phil.Core.DataProductKernelBridge` binds the product-specific certified residue:

1. exact-arity and successor-uniqueness facts are classified by the extracted elimination decision;
2. an arity rejection preserves `ProductArityMismatch`;
3. a duplicate-successor rejection is verified by the kernel, then the pre-existing native insertion path is allowed to produce its `DuplicateBinding` diagnostic;
4. only a kernel-accepted exact/distinct plan may reach successful restoration; and
5. successful restoration is postchecked against actual context state: every successor is installed under its exact ordered element mode/type, and every restricted product owner has been consumed. An unrestricted product satisfies the owner obligation by being unrestricted rather than by deletion.

Native failure always wins. Kernel disagreement can only reject.

## Closeout gate

The dedicated production-binding workflow:

- freshly extracts the exact kernel under Rocq 9.2.0 and byte-compares it with both checked-in copies;
- builds the ordinary library regression surface with `-Werror`;
- strictly typechecks the exact kernel, bridge, bound `DataMode`, direct correspondence harness, and production harness;
- runs the eight direct extracted-kernel controls;
- runs seven production-binding controls covering success, arity, duplicate-successor diagnostics, existing-name collision, restricted-owner consumption, exact successor contracts, and unrestricted-product reuse; and
- reruns the unchanged seven-case DATA-015 finite-product corpus.

## Residual native boundaries

Rocq extraction/toolchain correctness remains trusted. Concrete Haskell list ordering, `Name`/`Ty`/`ProductElementType`/`TyProduct` and `ResourceContext` representation, source-to-Core product elaboration, native map insertion/equality behavior, accepted unrestricted-product reuse, and concrete diagnostic payload construction remain native representation/runtime foundations.

A green merge promotes `PHIL-DATA-PRODUCT-001` to `Discharged / Implementation Refined`.
