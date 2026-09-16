# UTF-8 codec proof boundary v1

This note records the semantic-certification boundary for `PHIL-P1-IO-CODEC-001`.

## Owned semantics

`proof/Phil/Core/UTF8.v` certifies the Phil-level contract for explicit UTF-8 and convenience composition:

- a qualified UTF-8 codec has exact semantic-text round-trip;
- distinct Phil Unicode scalar sequences cannot be silently normalized into one encoded semantic Bytes value;
- encoded values remain members of the runtime-sized `Bytes` family;
- `read_utf8` retains the exact already-certified `FileSystem.read` predecessor;
- provider failures remain provider failures and are never relabeled as codec failures;
- a successful binary read whose explicit decode is invalid yields an explicit decode failure;
- `write_utf8` retains the exact already-certified `FileSystem.replace` over the exact encoded Bytes value;
- successful `write_utf8` is process-observable through the predecessor FileSystem semantics;
- failed `write_utf8` preserves the predecessor filesystem state;
- `write_line` appends exactly one LF semantic scalar and retains the exact already-certified Console write; and
- partial-write progress from Console is preserved unchanged by `write_line`.

`proof/Phil/Core/UTF8Implementation.v` owns only the finite production branch order: predecessor provider admission occurs first; decode classification occurs only after a successful binary read; provider failure bypasses decode; convenience writes introduce no new rejection after their predecessor call succeeds.

## Imported predecessor boundaries

The proof imports the already-certified semantics for:

- runtime-sized `Bytes`;
- provider-relative FileSystem state/read/replace behavior; and
- Console write semantics, including exact partial-write progress.

Authority possession, effect identity, path identity, boundedness, replacement observability, and Console occurrence semantics are therefore inherited rather than restated.

## Explicit representation / realization boundary

This certification does **not** claim that Rocq verifies the implementation of `Data.Text.Encoding` or `ByteString`. The `QualifiedUTF8Codec` boundary requires exact round-trip and non-normalizing injectivity for Phil semantic scalar sequences. Concrete correspondence from Haskell `Text`/`ByteString`/`RuntimeBytes` to that semantic codec, strict UTF-8 validity classification, host library correctness, and extraction/production binding remain later implementation-refinement or TCB evidence.

Locale, replacement-character fallback, Unicode normalization, host text mode, filesystem encoding, and implicit line-ending conversion are not inputs to the certified Phil codec semantics.

## Thread boundary

This PR is semantic certification only. It does not extract or production-bind a UTF-8 decision kernel. Any such production refinement belongs to the separate implementation-refinement lane.
