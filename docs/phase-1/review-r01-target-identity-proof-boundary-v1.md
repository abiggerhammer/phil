# PHIL-P1-REVIEW-R01 proof boundary

This slice certifies Astra Review R01: source-derived scalar values, compiler-synthetic scalar values, and block labels inhabit pairwise disjoint target identity namespaces, and each namespace is injective in its local identity.

The aggregate proof composes the existing Surface→Systems exact value-identity preservation boundary (PHIL-SURF-SYS-PROJ-001) with the conservative LLVM projection verifier (PHIL-LLVM-PRESERVE-001).

The concrete compiler correspondence remains executable:

- source bindings lower through `source.value.<encoded-name>` Systems ValueIds, where the source-name component is injectively ASCII-encoded before the stable LLVM sanitizer, and render in the `%source_value_...` namespace;
- direct-return temporaries lower through `synthetic.return.value.<n>` and render as `%synthetic_return_value_<n>`;
- blocks remain typed BlockIds and render in the block-label namespace (for the runnable path, `block_entry:`).

The permanent R01 regression deliberately uses hostile source spellings including `return_value_0`, `entry`, apostrophe versus underscore, Unicode identifiers, escape-looking spellings, and generated-temporary lookalikes.

The follow-up implementation remediation adds a concrete post-render check for duplicate or illegal unquoted local definitions on the public runnable compiler path, and the permanent workflow assembles the adversarial outputs with the project-resolved LLVM 18 assembler. The proof theorem itself is unchanged: concrete Text encoding, renderer correctness, GHC/runtime correctness, and LLVM toolchain behavior remain implementation/tool boundaries rather than retroactively becoming proof claims.
