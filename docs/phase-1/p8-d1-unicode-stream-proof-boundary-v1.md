# P8-D1 independent Unicode UTF-8 stream proof boundary

Controlling scope: issue #1770, maintainer authorization comment #6889430369 (2026-11-15), master #1584. This is **P8-D PR 1/2**, independent of the unused, blocked P8-C3 source/release slot and of P9 #1771/#1791. P10 #1772 remains blocked.

## Precisely modeled and checked

The Rocq 9.2 model extends the compiled P8-C1 **octet grammar**, not an invented native Text numerical ID. A scalar is a P8Utf8ScalarOctets constructor that passes the existing executable C1 strict 1/2/3/4-byte wellformedness check; a finite stream is a list of such constructors passing forallb p8_utf8_scalar_wellformed. Its encoder concatenates the original C1 scalar byte sequences without extra delimiter or normalization. Its decoder examines the lead byte to choose exactly one length, checks the **entire** C1 grammar, rejects incomplete/invalid octets and continues until all input bytes are consumed. Length-of-input fuel ensures termination without trusting a parser correctness axiom.

Named scope of proofs:

- **p8_d1_stream_roundtrip**: every valid finite C1 scalar-octet stream parses after encoding.
- **p8_d1_stream_canonical_acceptance**: every successful parse consists only of valid C1 scalar-octet constructors and re-encodes **exactly** to the original input.
- **p8_d1_stream_injective**: canonical stream encoding is injective on valid finite C1 scalar-octet lists.
- **p8_d1_encode_concat** and **p8_d1_canonical_concat_parse**: concatenation preserves the exact scalar boundaries, without byte padding or implicit normalization.
- **p8_d1_unique_stream_parse**: decoding is deterministic; no ambiguity in accepted scalar boundary splitting.

The compiled C1 one-scalar grammar rejects noncontinuation, overlong 2/3/4-byte sequences, surrogate encodings, out-of-range and scalar truncation. D1 additionally tests these when embedded in finite streams and at the trailing boundary. U+0000, U+00E9, U+1F642, U+10FFFF, decomposed U+0065+U+0301 and the empty stream receive direct executable examples. **Important:** an extra complete valid UTF-8 scalar is correctly accepted as another character; an invalid/truncated trailing scalar is rejected. Length framing belongs to the *separate* native diagnostic SemanticAtom envelope and must not be confused with a raw unframed Unicode string.

The path-scoped workflow compiles the full Rocq C1→D1 import closure, prints theorem assumptions, runs compiled rocq check, checksums proof objects/logs, builds real GHC 9.6.7 code with -Wall -Werror, and exercises the actual Data.Text.Encoding.encodeUtf8/decodeUtf8' and P8 diagnostic codec against independent boundary, multiscalar, NUL, malformed-middle/trailing and composition tests. Existing Haskell source/StageClosure/release controls remain unchanged and must pass.

## What has **not** been proved

The Coq octet constructor P8Utf8ScalarOctets is a **representation model**, not a Haskell Data.Text operational semantics or accepted native-to-Rocq bridge. GHC differential execution on finite samples does **not** prove universal native Text encoding/decoding, native Ord/Map/Set, the recursive SemanticForm structure, source IDs, checker events, manifest or P2/P6/P7 whole-release acceptance. No new TCB premise, source-language narrowing, chosen nat representation for native Text/Phil IDs, or caller-provided proof token is introduced. Universal native↔Rocq correspondence still requires a competent checked, explicitly defined Haskell library operational bridge (or separately reviewed assumption). P8-D2 may address independent structural proof after D1 actually merges; P8-C3 must still wait for P9's competent source/assurance/final use, SYS-012/013 and separate authorization. Do not infer FinalArtifactCertified, P10 readiness, signing, Phase 1 freeze or external auditor signoff.
