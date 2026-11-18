# P8-H8 — pure Unicode scalar canonicality and lexicographic order

Authority: [P8-H8 #1890](https://github.com/abiggerhammer/phil/issues/1890), subordinate to [P8 #1770](https://github.com/abiggerhammer/phil/issues/1770) and [P8-F #1810](https://github.com/abiggerhammer/phil/issues/1810). This adds **only pure mathematical Rocq** theorems; it does not modify or attest native Haskell, production acceptance, GHC/foreign-library operations, compiler flags, the TCB, or the Phase 1 release.

## Exact model domain

An admitted scalar is a `P8Utf8ScalarOctets` constructor for which the **pre-existing** `p8_utf8_scalar_wellformed` predicate returns `true`. Its octets and numeric value are those of unchanged C1 `P8UnicodeUtf8Model.v`. Admitted Unicode numbers satisfy the unchanged `p8_unicode_scalar` (0..0x10FFFF, excluding surrogates). A D1 stream is a **finite list of wellformed scalar constructors** accepted by unchanged `p8_d1_valid`. `p8_d1_encode` concatenates their octets. The byte comparator is unchanged D2 `p8_d2_compare_bytes`, not wire-tag ordering, not a Haskell `Ord Text` instance.

## Universal theorems

The new `P8H8UnicodeScalarOrder.v` proves:

1. `p8_h8_c1_valid_scalar_value`: every wellformed original C1 constructor computes to an admitted Unicode scalar.
2. `p8_h8_numeric_encoder_value`, `p8_h8_numeric_encoder_wellformed` and `p8_h8_numeric_encoder_admitted`: the constructive 1–4-byte quotient/remainder encoder maps **every admitted numeric scalar** to a wellformed constructor with exactly the original value; the total numeric encoder preserves its numeric input. These are not enumeration-based proofs.
3. `p8_h8_wellformed_width_bounds`, `p8_h8_c1_value_injective_on_valid` and `p8_h8_encoder_c1_inverse`: no two wellformed **original C1** constructors share a numeric scalar value, and canonical numeric encoding inverses the original C1 interpretation.
4. `p8_h8_scalar_bytes_numeric_compare` and `p8_h8_scalar_byte_less_iff` / `p8_h8_scalar_byte_eq_iff`: comparing the canonical octets of any two wellformed C1 scalars agrees exactly with `Nat.compare` of their numeric values (including equality and strict inequality).
5. `p8_h8_byte_compare_equal_width_suffix`, `p8_h8_scalar_byte_append`, `p8_h8_d1_stream_lex_numeric_compare` and `p8_h8_d1_stream_strict_lex_iff`: finite valid D1 concatenated byte streams compare exactly like the lexicographic sequences of numeric scalar values, including empty sequences, proper prefixes and identical streams.

Discriminating executable model examples cover U+0000, 007F/0080, 07FF/0800, D7FF/E000, FFFF/10000, 10FFFF, U+00E9 versus `e` followed by U+0301, and rejection of overlong, surrogate and beyond-range encoded octets. The proofs use the existing C1 E0/ED/F0/F4 byte guards and do not normalize Unicode.

## Reproducible proof check

`.github/workflows/phase1-p8-h8-scalar-order.yml` uses Rocq **9.2.0**, compiles unchanged C1/D1/D2 and new H8 in order, executes each named `Print Assumptions`, recursively checks all four compiled objects with `rocq check`, scans for new axiom/admission declarations, and emits source/object/assumption-log SHA-256 receipts.

Historical scratch-only proof precursor `fb9ab540b56447fe746e947e52a64071b3c5ccfd` passed [Rocq run 44308472354](https://github.com/abiggerhammer/phil/actions/runs/44308472354), including 16 named closed-context assumptions and all C1/D1/D2/H8 object checks. That scratch result is **not** a substitute for green checks on this PR's exact head; the PR must earn its own full receipt.

## Explicit exclusions

This theorem establishes properties of modeled **canonical UTF-8 octets**, **not** `Data.Text` comparison, actual GHC packages, `Map`/`Set` invariants, Haskell diagnostic codec operational semantics or accepted native-to-Rocq transport. Original P8-F2 0/1 stays stopped pending separately authorized trusted/native proof obligations. Independent selected-build gate [#1826](https://github.com/abiggerhammer/phil/issues/1826) and T1–T4 gate [#1827](https://github.com/abiggerhammer/phil/issues/1827) remain open. P8-C3, P10 and Phase 1 freeze are not unlocked.

Mutual D2 recursive compare algebra, Eq coherence, and adjacent-versus-pairwise container order are proposed **H9**, not proved or authorized by H8.
