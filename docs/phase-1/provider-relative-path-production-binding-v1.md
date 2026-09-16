# Provider-relative Path production binding v1

The production binding for `PHIL-P1-IO-PATH-001` uses the Haskell module extracted from `ProviderRelativePathImplementation.v` through `ProviderRelativePathImplementationExtraction.v`.

Canonical checked-in kernel:

- path: `src/ProviderRelativePathKernel.hs`
- byte length: 3216 bytes
- SHA-256: `ae168907b3a5e28793beca30d802ab3345ac7c37a02b2f241acc0c8a7abbf1d4`

CI fresh-extracts the kernel, compares it byte-for-byte with the checked-in production copy, verifies the fixed digest, compiles it under `-Wall -Werror`, runs direct branch-order controls, builds the complete Cabal regression substrate, strict-typechecks `Phil.Systems`, and reruns the unchanged IO-PATH corpus.

`Phil.Systems` is responsible only for extracting concrete `Data.Text` facts and reconstructing existing Haskell values/errors from the extracted decision. It does not independently choose admission or rejection order.

The binding deliberately does not certify host filesystem realization. Host separators, drive conventions, working-directory lookup, normalization, symlink handling, and filesystem effects remain outside provider-relative Path identity.
