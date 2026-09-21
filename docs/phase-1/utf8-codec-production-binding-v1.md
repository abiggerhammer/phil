# PHIL-P1-IO-CODEC-001 — production binding

This closeout mechanically binds the already-Certified UTF-8 composition decision semantics to the existing production `Phil.IO.UTF8` APIs.

## Exact staged kernel

PR #1270 staged `UTF8ImplementationExtraction.v` and produced the exact green Rocq 9.2 extraction:

- file: `UTF8ImplementationKernel.hs`
- size: **1,288 bytes**
- SHA-256: `161c8ed498d026763b38db994a52ac620a2654d9c59461ef13e5b8f02515d5fb`
- staging artifact ID: `10651156551`
- staging artifact digest: `sha256:9855a4a955d00ce022d4b1f8666d56a4523641809a40ba8707e7b0f758626174`

`generated/UTF8ImplementationKernel.hs` and `src/UTF8ImplementationKernel.hs` are byte-identical copies of those extracted bytes. The closeout workflow freshly re-extracts and refuses size, digest, or byte drift.

## Refined predecessors

Both provider predecessors are already mechanically production-bound:

- `PHIL-P1-IO-FS-001`: Discharged / Implementation Refined;
- `PHIL-P1-IO-CONSOLE-001`: Discharged / Implementation Refined by #1267.

The codec layer does not duplicate either predecessor's provider, authority, effect, failure, or observability semantics.

## Native-first production binding

`UTF8CheckError` distinguishes:

- exact wrapped FileSystem predecessor errors;
- exact wrapped Console predecessor errors; and
- codec-kernel disagreement after native predecessor success.

### read_utf8

`checkReadUTF8`:

1. executes the production-refined FileSystem read checker;
2. preserves any native predecessor rejection as `UTF8FileSystemError`;
3. classifies a checked provider success through the existing strict `utf8Decode`;
4. reflects predecessor acceptance, provider success/failure, and decode success/failure into the extracted kernel;
5. requires exact kernel classification agreement; and
6. reconstructs the unchanged checked predecessor plus codec outcome.

Provider failure therefore cannot become decode failure, and invalid UTF-8 cannot become provider failure.

### write_utf8

`checkWriteUTF8`:

1. performs the existing explicit `utf8Encode`;
2. executes the production-refined FileSystem replace checker;
3. preserves any predecessor rejection as `UTF8FileSystemError`;
4. requires the extracted composition gate to accept the successful predecessor; and
5. returns the unchanged text, bytes, and checked replace record.

### write_line

`checkWriteLine`:

1. appends exactly the existing single LF;
2. executes the production-refined Console write checker;
3. preserves any predecessor rejection as `UTF8ConsoleError`;
4. requires the extracted composition gate to accept the successful predecessor; and
5. returns the unchanged requested text and checked Console write.

## Codec primitive boundary

This implementation refinement binds the **composition/classification semantics** mechanically. The Certified UTF-8 semantic proof deliberately treats the actual codec implementation as a qualified representation/realization boundary.

Therefore the following remain explicit native/TCB facts rather than being silently promoted into Rocq theorems:

- correctness of `Data.Text.Encoding.encodeUtf8` and `decodeUtf8'`;
- Haskell `Text` / `ByteString` / RuntimeBytes representation;
- Unicode scalar validity and library behavior;
- absence of normalization/replacement fallback in those selected APIs;
- GHC/runtime correctness; and
- Rocq extraction/toolchain correctness.

Locale, host text mode, implicit filesystem encoding, Unicode normalization, replacement-character fallback, and line-ending conversion remain non-semantic by construction.

## Permanent evidence

The production-binding workflow:

1. freshly compiles/extracts the UTF-8 proof chain under Rocq 9.2;
2. requires the exact 1,288-byte / SHA-256 kernel;
3. byte-compares fresh extraction against both checked-in copies;
4. reruns all 12 direct extracted-kernel controls;
5. strict-typechecks and executes the bound production surface;
6. replays the unchanged IO-CODEC corpus;
7. reruns the implementation-refined FileSystem and Console predecessor corpora; and
8. records exact production identities as a retained artifact.

A fully green exact-head merge permits `PHIL-P1-IO-CODEC-001` to move from **Active / Certified** to **Discharged / Implementation Refined**.
