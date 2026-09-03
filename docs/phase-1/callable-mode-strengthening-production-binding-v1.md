# Callable Mode Strengthening production binding v1

`PHIL-CALL-MODE-STRENGTHEN-001` is production-bound to the exact Rocq-extracted `CallableModeStrengtheningKernel.hs` staged by PR #627.

## Exact kernel identity

- staging exact green head: `4a2bb4cb7d614b2eed124b5750f5a216a9f54a54`
- staging merge: `7d021a4c5f3dc978e567b0599cd1738021f5d700`
- staging run: `33794278387`
- staging artifact: `9908619177`
- artifact digest: `sha256:526eb96c5dd04535bfb6e6d9fd2d6f732db89f9a349f2eab840681a30af6b13a`
- exact kernel SHA-256: `f985e64a008d0202a63f548da824a11ce8ef15e1a6aa7e1ab7aa3489861ee25e`
- exact kernel Git blob: `9be4285e723c5aa18eda7239772ae13d67ced23c`

The generated and source-tree kernel copies are byte-identical to the staging artifact, and the production workflow freshly regenerates the kernel from Rocq before testing the Haskell binding.

## Extracted semantic ownership

The exact kernel owns the final classification of reflected closure-mode facts with the same precedence as the Certified model and pre-binding native implementation:

1. capture-minimum weakening rejects;
2. explicit equality with the capture minimum accepts before justification inspection;
3. strict mode without a justification rejects;
4. target-implementation-only justification rejects;
5. semantic justification bound to the wrong callable contract rejects;
6. exact-contract semantic justification with empty detail rejects;
7. exact-contract nonempty lifecycle or authority justification accepts strict strengthening.

The exact kernel also owns the checked-result shape postcheck for minimum mode, selected mode, and justification identity. Production `Phil.Core.Callable.ModeDeclaration` derives concrete native facts, routes the classification through the extracted kernel, preserves the existing native diagnostic associated with each classification, constructs the checked value only on extracted acceptance, and then requires the extracted checked-shape classifier to accept that value. Any impossible bridge disagreement fails closed as `ClosureModeStrengtheningKernelDisagreement`.

## Native boundary retained

The following remain native and explicit correspondence/predecessor boundaries:

- closure capture discovery and the already-Certified capture-derived minimum from `PHIL-CALL-MODE-001`;
- concrete Haskell `Mode` representation and `modeRank` correspondence;
- `InterfaceRevision` and `Text` representation/equality and empty-text detection;
- construction of `CheckedClosureMode` and exact native diagnostic payloads;
- the concrete `ClosureCaptureSummary`, which is preserved byte-for-value by construction but is outside the Rocq checked-shape record;
- source elaboration into callable contracts, captures, declarations, and justifications;
- truth and competence of referenced lifecycle or authority obligations;
- GHC/runtime correctness and the Rocq extraction toolchain.

The extracted gate may reject production execution on a kernel/native disagreement; handwritten code cannot turn an extracted rejection into success.

## Closeout gate

The production gate:

- freshly compiles `GenericStructural.v`, `CallableMode.v`, the Certified `CallableModeStrengthening.v`, and the implementation correspondence proof;
- freshly extracts the kernel and requires SHA-256 `f985e64a008d0202a63f548da824a11ce8ef15e1a6aa7e1ab7aa3489861ee25e`;
- byte-compares both checked-in kernel copies against the fresh extraction;
- strictly typechecks the exact kernel, bridge, production checker, direct correspondence harness, production-binding harness, and unchanged CALL-017 corpus;
- executes all fourteen direct extracted-kernel controls;
- executes fifteen production-binding controls, including exact capture-summary preservation and native diagnostic preservation;
- reruns the unchanged eight-case CALL-017 corpus.

A fully green merge promotes `PHIL-CALL-MODE-STRENGTHEN-001` from `Discharged / Certified` to `Discharged / Implementation Refined`.
