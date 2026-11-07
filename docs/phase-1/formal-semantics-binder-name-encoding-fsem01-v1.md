# FSEM-01 — exact local-binder Core.Name encoding (first correspondence slice)

> **Status:** bounded Rocq encoding theorem plus executable Haskell
> representation conformance, **not** a proof of the whole Grammar-v1
> source-to-Core elaborator or the Haskell implementation of Unicode Text.
> Tracks [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613)
> and builds on the [conditional linear-loan model](formal-semantics-exact-loan-transition-model-fsem01-v1.md).

## Why it matters

The production [BinderScope.hs](../../src/Phil/Surface/GrammarV1/BinderScope.hs)
allocates one semantic key:

~~~text
GrammarV1BinderKey (DeclarationKey rootText) ordinal
~~~

It derives the internal Core.Name from the **declaration root and ordinal**,
not the display spelling or source span:

~~~text
"$phil.local:" ++ show(Text.length(rootText)) ++ ":" ++ rootText ++ ":" ++ show(ordinal)
~~~

Length prefixing is essential: a root can contain colons, numbers, delimiter-
looking substrings, newlines, and Unicode without confusing the following
ordinal with a piece of the root. A view binder is allocated after its owner
under a monotonically advanced ordinal; equal source display names in distinct
lexical scopes must not alias Core owner identities.

The earlier [SurfaceBorrowLoanStateCorrespondence.v](../../proof/Phil/Surface/SurfaceBorrowLoanStateCorrespondence.v)
proved conditional loan-membership preservation under an **injective**
`nameOf : BinderKey -> Core.Name`. The present slice characterizes a
concrete name encoding and establishes part of the injection premise.

## New Rocq model and theorem

[SurfaceBinderNameEncoding.v](../../proof/Phil/Surface/SurfaceBinderNameEncoding.v)
is an executable ASCII/Rocq-string model of the exact delimiter and
length-prefix shape. It renders numbers using
`DecimalString.NilEmpty.string_of_uint (Nat.to_uint n)`; parsing uses the
matching standard-library conversion. It:

- strips the literal `$phil.local:` prefix;
- splits the **decimal root-length token** at its first colon;
- consumes exactly that number of root characters rather than splitting on a
  colon inside the root;
- consumes the final colon and decodes the ordinal.

Proved statements include:

| Theorem | Scope |
| --- | --- |
| `read_render_nat` | Standard-library decimal serialization roundtrips natural numbers |
| `strip_prefix_self`, `split_render_nat`, `take_exact_root` | Prefix and length-delimited parsing return precisely their original components |
| `decode_encode_binder_name` | Every encoded ASCII/Rocq-string root and natural ordinal decodes to its original pair |
| `encode_binder_name_injective` | Equal canonical names force **both** roots and ordinals to be equal, not merely equal types |
| `encode_text_binder_key_injective` | The structural `(root, ordinal)` representation has exact name injectivity |
| `model_name_of_injective` | The existing normalized `BindingSemantics.BinderKey = (nat, nat)` can use this concrete encoder **if** its `declarationText : nat -> string` mapping is injective |

The final theorem discharges the *name-encoding injectivity argument for this
chosen model* conditional on a separate declaration-root representation
hypothesis. It does **not** prove the Haskell `DeclarationKey` representation
is equivalent to the proof's `DeclarationIdentity := nat`, or that the
Haskell source decoder implements the Rocq decoder for every Unicode input.

## Haskell producer and executable evidence

The existing code path that fills
`grammarV1ResolvedBinderCoreName` now invokes an exported
`grammarV1BinderCoreName` function: this is the **same producer**, not a
parallel encoder used only by tests. A new
`grammarV1DecodeBinderCoreName` accepts a `Name` only if it is canonical,
with a bounded, nonnegative `Int` length and ordinal, and re-encodes to
**exactly** the original name. It is diagnostic/correspondence tooling; it
does not change source-name admission or substitute for lexical resolution.

The dedicated
[Phase1FSEM01BinderNameMain.hs](../../test/Phase1FSEM01BinderNameMain.hs)
test exercises the actual producer/decoder on:

1. Cartesian combinations of root strings and nonnegative ordinals,
   including `maxBound :: Int`, and checks all encoded names differ for
   distinct sample keys.
2. Empty roots, misleading `$phil.local:` substrings, embedded colons,
   newlines, and a root containing NUL.
3. Single-scalar and multiple-scalar Unicode roots: `é`, combining marks,
   `🐈`, `👩‍💻` and `猫:fish`. The asserted `Text.length` values
   are Unicode code-point counts, **not UTF-8 byte counts**.
4. Rejection of leading-zero lengths and ordinals, signs, missing separators,
   incorrect lengths, trailing junk and decimal overflow.

[The dedicated FSEM-01 CI workflow](../../.github/workflows/fsem01-binder-name-encoding.yml)
compiles the proof with Rocq 9.2, prohibits `Admitted`/global axioms in
the new file, builds the production Haskell library with `-Werror`, and
strictly checks/replays the new tests. All conclusions are conditional on
that workflow being **green on the exact final PR head**.

## What remains deliberately unproved

- **Haskell Text ↔ Rocq String:** The Rocq model's `String.length` counts
  ASCII-chain characters. `Data.Text.length` counts Unicode code points
  in valid Haskell Text. Unicode examples are executable *tests*, not a
  theorem about the two libraries or their encoding/decoding semantics.
- **Machine Int:** The model's ordinal is `nat`, while the producer uses
  `Int` and creates only nonnegative ordinals by monotonic allocation.
  Integer bounds, overflow behavior and the complete allocator are not
  theorems of this file.
- **Declaration identities:** The normalized Rocq root is `nat`; actual
  `DeclarationKey` is `Text`. The conditional injection
  `declarationText_injective` is **not silently erased**.
- **Production resource transitions:** Existing #1626 production traces
  and #1627 conditional loan proofs remain distinct. This slice does not
  certify Haskell finite-map/set operations, escaping values, the
  `BorrowEscape` diagnostic or the source-to-Rocq simulation relation.
- **Normative authority:** This is a reviewable engineering/proof slice,
  not a new language typing rule, full compiler preservation theorem, or
  discharge of source `satisfies C`.

## Next soundness step

Build a bounded, explicitly trusted `DeclarationKey` representation bridge
(or a more direct refinement to the Haskell `Text` encoding), then compose
it with the established name injection and the exact source-derived
production trace. Only after preserving **identity, loan membership, step
outcomes, and the rejected `BorrowEscape` prefix** can the FSEM-01
source-to-model simulation obligation be narrowed or discharged.
