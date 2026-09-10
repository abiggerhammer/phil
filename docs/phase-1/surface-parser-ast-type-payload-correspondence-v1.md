# Phase 1 surface parser AST type-payload correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #885.

The preceding slices established the certified source/token/tree bridge, production admission, outer source and declaration structure, the `type_alias_decl` shell, generic parameters and requirements, shallow type-constructor correspondence, static references, and structural static-value expressions. This slice makes the type correspondence recursive for the parts whose dependencies are now available.

## Correspondence established here

For every accepted type-alias target exercised by the direct controls and the Phase 1 surface corpus, the certified parse tree and production AST are projected to the same span-insensitive recursive type payload:

- `Unit`, `Bool`, and exact primitive spellings (`Char`, `String`, `U*`, `I*`, `F32`, `F64`);
- `Bytes`, with **runtime-sized bare `Bytes` distinguished from explicitly indexed `Bytes[expression]`**;
- `Frame[static_reference]`, using the #883 static-reference projection;
- `Proof[proposition]`, with the proposition slot structurally required but intentionally opaque in this slice;
- `Validated[static_reference, expression, expression]`, preserving the validator reference and structurally requiring both expression slots;
- refinement types, preserving the binder and recursively translating the base type while structurally requiring the proposition slot;
- tuple types, recursively translating every element; and
- named types, preserving the full #883 static-reference spine.

The bare-`Bytes` production representation is not treated as source syntax. Production represents runtime-sized `Bytes` with the unspellable `runtimeBytesLengthMarker`; this projection maps that marker back to `GrammarV1ReferenceRuntimeBytes`, while any source-present `Bytes[...]` index maps to `GrammarV1ReferenceIndexedBytes`. The certified tree never contains the marker.

## Evidence boundary

This is still a correspondence/test layer, not a new Rocq theorem. It deliberately does **not** claim payload equivalence for:

- ordinary `expression` nodes inside `Bytes[...]` or `Validated[...]`;
- `proposition` nodes inside `Proof[...]` or refinement types;
- nested session/effect payloads inside static-reference arguments; or
- the remaining declaration-family bodies.

Those slots remain explicit typed holes rather than being interpreted or erased. The static-reference payloads reused here retain the #883 grammar-category boundary; static-value structure itself is separately closed by #885.

Accordingly `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted. Successor slices should close ordinary expression and proposition structure, then feed those translations back into the remaining type holes and declaration families.
