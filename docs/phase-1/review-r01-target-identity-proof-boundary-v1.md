# PHIL-P1-REVIEW-R01 proof boundary

This slice certifies Astra Review R01: source-derived scalar values, compiler-synthetic scalar values, and block labels inhabit pairwise disjoint target identity namespaces, and each namespace is injective in its local identity.

The aggregate proof composes the existing Surface→Systems exact value-identity preservation boundary (PHIL-SURF-SYS-PROJ-001) with the conservative LLVM projection verifier (PHIL-LLVM-PRESERVE-001).

The concrete compiler correspondence remains executable:

- source bindings lower through `source.value.<name>` Systems ValueIds and render as `%source_value_<name>`;
- direct-return temporaries lower through `synthetic.return.value.<n>` and render as `%synthetic_return_value_<n>`;
- blocks remain typed BlockIds and render in the block-label namespace (for the runnable path, `block_entry:`).

The permanent R01 regression deliberately uses hostile source spellings such as `return_value_0` and `entry` to pressure source/synthetic and value/block collisions.

Concrete Text escaping/sanitization, Systems/LLVM container representation, renderer correctness, GHC/runtime correctness, and LLVM toolchain behavior remain explicit implementation boundaries.
