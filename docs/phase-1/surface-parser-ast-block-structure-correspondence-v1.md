# Grammar-v1 block-structure AST correspondence

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #897 by factoring the shared block/match substrate used by the remaining seven block-bearing command families.

The production-side projection and certified-tree decoder cover:

- `block` and ordered `statement` structure;
- all three statement forms: `let`, `return`, and expression statements;
- identifier, tuple, and record patterns;
- record field-pattern names and optional nested pattern values;
- `match_arm` block-vs-statement bodies;
- tuple and record case binders, including field aliases and trailing-comma normalization;
- `join_clause` state slots and optional invariants; and
- loop `state_binding` names, optional types, and initializers.

Nested ordinary expression payloads reuse #889's expression-core correspondence, proposition payloads reuse #891, and type payloads reuse #887. Consequently a nested command expression inside a block is still represented through #889's explicit command-family boundary rather than recursively decoded by this slice.

This is intentional: the next command slice can reuse one shared structural decoder for `borrow`, `if`, `match`, `decide`, `closure`, `loop`, and `offer`, after which a separate integration pass can remove the remaining mutually recursive command/expression/type/static-argument boundaries.

`PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**. This slice does not by itself justify promoting `PHIL-ASSURE-IMPL-CORR-001` to Implementation Refined.
