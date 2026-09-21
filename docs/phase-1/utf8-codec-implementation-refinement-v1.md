# PHIL-P1-IO-CODEC-001 — implementation refinement staging

This slice stages mechanical implementation refinement for the already-Certified explicit UTF-8 codec/composition semantics. It does not change production `Phil.IO.UTF8` behavior.

## Certified predecessor

`proof/Phil/Core/UTF8.v` already owns the semantic claims for:

- exact UTF-8 round-trip for a qualified codec;
- non-normalizing injective encoding of distinct scalar sequences;
- runtime-Bytes result classification;
- exact preservation of the checked FileSystem.read predecessor;
- explicit invalid-decode classification;
- exact text preservation on successful decode;
- exact FileSystem.replace composition for `write_utf8`;
- exact one-LF append for `write_line`; and
- preservation of Console partial-write progress.

The FileSystem and Console predecessors remain independently certified authorities. Console is now also production-refined by #1267.

## Executable decision surface

`UTF8Implementation.v` owns only the finite production branch order:

1. a rejected predecessor blocks all codec-level classification;
2. provider failure is preserved before decode classification;
3. successful provider + successful decode classifies decoded;
4. successful provider + failed decode classifies decode failure;
5. `write_utf8` introduces no rejection after an accepted FileSystem.replace predecessor; and
6. `write_line` introduces no rejection after an accepted Console write predecessor.

This staging pass adds exact iff characterizations for all four read outcomes and both convenience-write acceptance gates.

`UTF8ImplementationExtraction.v` extracts those decisions as `UTF8ImplementationKernel.hs`.

## Staging gate

The permanent `Phase 1 IO Codec Proofs` workflow now:

- compiles the semantic and implementation proof chain under Rocq 9.2.0;
- freshly extracts `UTF8ImplementationKernel.hs`;
- records the exact kernel bytes with the proof artifact;
- compiles and executes 12 direct extracted-kernel controls under `-Wall -Werror`;
- replays the unchanged IO-CODEC UTF-8/convenience corpus; and
- reruns the FileSystem and now production-refined Console predecessor corpora.

This tranche deliberately does **not** check the extracted kernel into `src/` or alter `Phil.IO.UTF8`.

## Retained native boundary

The extracted decision kernel does not claim correctness of:

- `Data.Text.Encoding.encodeUtf8` / `decodeUtf8'`;
- `Text` or `ByteString` concrete representation;
- Unicode scalar validity or normalization libraries;
- RuntimeBytes representation;
- FileSystem provider realization;
- Console provider realization;
- concrete authority/effect identities;
- diagnostics; or
- GHC/Rocq extraction/runtime correctness.

## Next tranche

After a fully green exact staging head, production binding will harvest the exact extracted bytes, check byte-identical copies into `generated/` and `src/`, and gate native-success composition paths fail-closed while retaining native predecessor diagnostics and result construction.

Only that later production-binding closeout promotes `PHIL-P1-IO-CODEC-001` from **Certified** to **Implementation Refined**.
