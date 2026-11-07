# FSEM-01 — source-derived observation wire v1 and formally checked decoder

> **Status:** bounded, non-normative evidence bridge; the first exact-byte
> producer → artifact → Rocq decoder control for the admitted single-owner
> `Bytes[8]` loan fragment. This does **not** establish that the whole
> Haskell checker refines the Rocq model, or that all possible source
> programs have a trace. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## The concrete artifact

The producer is
[`test/Phase1FSEM01ObservationWireMain.hs`](../../test/Phase1FSEM01ObservationWireMain.hs).
It reads **actual UTF-8 Grammar-v1 source fixtures** from
[`test/fixtures/fsem01-observation-v1/`](../../test/fixtures/fsem01-observation-v1),
calls `grammarV1CheckedBorrowResourceFunctionTrace` and the ordinary
production checker, verifies they agree, and captures actual owner/view
Core names, linear-owner presence, shared-loan membership and the exact
terminal outcome.

The wire is one **ASCII-only** `PHIL-FSEM01-OBS-V1|` header followed by
**eight consecutive length-framed fields**. Each frame is the canonical
base-10 character count, a colon, then exactly that many ASCII characters,
with no field separators or trailing bytes. The fields, in order, are:

| Field | Concrete contents |
| --- | --- |
| 1 | Lowercase, 64-character SHA-256 hex of the exact UTF-8 source bytes |
| 2 | Lowercase UTF-8 hex for the exact `DeclarationKey` root |
| 3 | Lowercase UTF-8 hex for the actual owner `Core.Name` |
| 4 | Lowercase UTF-8 hex for the actual borrow-view `Core.Name` |
| 5 | Canonical nonnegative decimal owner ordinal |
| 6 | Canonical nonnegative decimal borrow-view ordinal |
| 7 | Exact observed checkpoint sequence as short ASCII state codes |
| 8 | Outcome code: `OK:Bytes8` or the exact production `BorrowEscape` diagnostic |

The two admitted trace codes are:

- Success: `B10,S11,N11,C10,R00`.
- Escaping borrowed view: `B10,S11,E11,X11`.

The first letter is the phase: before, started, normal body result,
escaping body result, closed, terminal returned, or rejected. The two
digits record **linear owner present** and **loan active**, respectively.
Neither error path has a `C` or `R` checkpoint. The error outcome is
`ERR:BorrowEscape:shared view escapes its lexical scope`.

All fields are ASCII even when the source declaration root or generated
names contain Unicode; those values are UTF-8 **hex**, not raw Rocq
`String` characters. The token list and ordering are versioned: unknown
versions fail closed, rather than guessing compatibility.

## Actual emitted files and reproducibility

[The dedicated workflow](../../.github/workflows/fsem01-observation-wire.yml)
creates a downloadable GitHub Actions artifact named
`fsem01-source-observation-v1` containing:

- `positive-ascii.obs` and `escape-ascii.obs` for a normal root;
- `positive-unicode.obs` and `escape-unicode.obs` for
  `decl.é:猫`.

The files are created anew from the checked production interpreter
**on the CI commit**, not from hand-written expected trace text or from
a Rocq model evaluator. The fixed source fixtures and their SHA-256
digests bind each specimen to specific source bytes; the output is
deterministic and does not include a wall-clock timestamp.

An independent [Python validator](../../scripts/fsem01_observation_wire.py)
checks the emitted source digests against the fixture files, canonical
lengths, lowercase hex, UTF-8 decoding and generated name roots/ordinals,
the exact allowed checkpoint paths, terminal outcome and file set.
It refuses extra artifacts. These controls are *tests*, not proof of
Python or Haskell correctness. SHA-256 is an integrity fingerprint,
not a signature or authentication of the compiler.

## The machine-checked decoder

[SurfaceObservationWire.v](../../proof/Phil/Surface/SurfaceObservationWire.v)
defines a **total decoder of raw ASCII wire strings** with explicit
frame lengths and a fixed number of fields. It validates:

- the exact v1 header, eight fields, complete byte consumption, and
  canonical framing (no leading-zero lengths or trailing material);
- a 64-character lowercase-hex source digest;
- even-length lowercase-hex identity carriers and canonical decimal
  owner/view ordinals, with owner ordinal less than view ordinal;
- one of the two permitted exact checkpoint/outcome combinations.

Its key theorems are
`parse_frame_roundtrip`, `parse_pack_fields`,
`decode_encode_valid_artifact`, `decoded_artifact_is_valid`,
`decoded_artifact_has_consistent_outcome`, and
`decoder_rejects_wrong_version`. These statements concern the
**Rocq wire codec**, not Haskell UTF-8/SHA implementation correctness.
The decoder's validation alone does not cryptographically bind a root to
a source; that is checked against real sources by CI.

Crucially, the Rocq CI job **downloads the actual Haskell-produced
artifacts**, revalidates their source bindings, and generates a literal
Rocq module containing each artifact's *exact bytes*. The module proves
via `vm_compute` that `decodeArtifact` accepts each specimen and
extracts its required trace and terminal outcome. No generated source
or arbitrary artifact bytes are evaluated as code: the witness generator
allows only a strict ASCII literal alphabet without quotes, backslashes
or newlines. The compiled proof object and every specimen have SHA-256
digests in the CI log.

Reproduction on the checked commit:

~~~sh
cabal build lib:phil-core --ghc-options=-Werror
cabal exec -- runghc -isrc -Wall -Werror test/Phase1FSEM01ObservationWireMain.hs
cabal exec -- runghc -isrc -Wall -Werror test/Phase1FSEM01ObservationWireMain.hs --emit fsem01-wire-artifacts
python3 scripts/fsem01_observation_wire.py --artifact-dir fsem01-wire-artifacts --rocq-witness fsem01-wire-generated/GeneratedObservationWitness.v
~~~

The Rocq step of the workflow compiles the full dependency chain and
the generated witness with Rocq 9.2.0. Unlike earlier handwritten
snapshot-only tests, this checks the **exact serialized bytes emitted
by the real source-derived checker** at the decoder boundary.

## Explicitly open obligations

1. The specimen producer is still Haskell code; no theorem forces all
   checker paths or every `containsBorrowedView` call to emit correct
   artifacts. A passing control covers only the admitted fixtures.
2. The accepted root catalog is bounded. Neither its provenance across
   edits nor a persistent, universal `DeclarationKey → nat` relation
   has been proved.
3. Rocq `String` sees ASCII wire text; validity of arbitrary UTF-8
   hex and correspondence to `Data.Text` are tested by Python/Haskell,
   not formally verified as a Unicode theorem. Hash collision
   resistance is an external cryptographic assumption.
4. The decoder proves syntactic/semantic *wire validity* but not the
   source small-step soundness theorem for Haskell evaluation. The
   transition/no-error-successor result in
   [#1637's model](formal-semantics-step-error-bridge-fsem01-v1.md)
   remains distinct from a full implementation-refinement proof.
5. No inference is made about affine, nested or captured borrows,
   continuations after arbitrary errors, joins/backedges, scheduling,
   effects, or the source `satisfies C` obligation.

**Next target:** use versioned trace evidence to specify a
source-to-model simulation relation for the admitted fragment, stating
precisely which producer/decoder properties are trusted and which
properties are proved. Do not graduate a normative rule yet.
