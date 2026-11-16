# P8-F1 — universal finite canonical structural-wire inversion

Owner: `lane: p8-representation`; controlling [#1810](https://github.com/abiggerhammer/phil/issues/1810). This independent F1 tranche does **not** renew E1/E2 or authorize the unused, blocked P8-C3 slot.

## Exact pure-model theorem scope

`proof/Phil/Verification/P8F1RecursiveInverseModel.v` imports the immutable D1 Unicode stream, D2 mutual structural/order domain, E1 executable wire codec, and E2 normalization models. The new proofs work against the **actual E1 definitions**, without a replacement parser, a caller-supplied parser-success proposition, axioms, admitted cases, or an invented native Text representation.

- `p8_f1_frame_count_roundtrip`: for every finite natural number `n` and every byte suffix, `p8_e1_read_count (p8_e1_frame_count n ++ suffix) = Some (n, suffix)`. Supporting lemmas prove the actual E1 division/remainder decimal emitter's value and canonical digits.
- `p8_f1_text_prefix_roundtrip`: every D1-valid UTF-8 octet stream, including empty, NUL, non-ASCII and supplementary scalars, has an exact framed-text prefix/remainder inverse.
- `p8_f1_forms_count_fits_canonical_wire` and `p8_f1_fields_count_fits_canonical_wire`: each finite emitted collection has sufficient bytes for E1's declared-count guard.
- `p8_f1_forms_loop_complete_from_children` and `p8_f1_fields_loop_complete_from_children`: exact captured-fuel E1 local parser count loops recover every finite valid form/field list under an explicit sufficient child-fuel premise. The proof-only transparent loops match E1's local `let fix` closures by kernel conversion.
- `p8_f1_form_prefix_fuel_bound`: for every D2-valid finite form `f`, arbitrary suffix, and `fuel >= length (p8_e1_put_form f)`, the actual `p8_e1_parse_form_fuel fuel (p8_e1_put_form f ++ suffix)` returns `Some (f, suffix)`. Induction is on fuel; each nested child consumes a constructor tag, hence its serialized length is strictly smaller. All four constructors are covered: Atom, Ordered, Unordered and Record.
- `p8_f1_universal_model_roundtrip`: `p8_d2_valid_form f = true -> p8_e1_decode_form (p8_e1_put_form f) = Some f`, for **all** finite normalized D2 forms.
- `p8_f1_universal_model_injective`: equal encodings of two D2-valid forms entail structurally equal forms.
- `p8_f1_universal_model_trailing_rejected`: a nonempty suffix appended to a D2-valid emitted form causes the whole-form decoder to reject.
- `p8_f1_universal_normalized_wire_roundtrip`: normalization of a valid canonical encoding returns that exact form. No set/record sorting or silent key deduplication occurs in this theorem; D2 validity requires pairwise strict order and unique keys upfront.

Rocq 9.2.0 must compile the complete C1/D1/D2/E1/E2/F1 dependency chain, check these named assumptions (no new Axiom/Admitted/Parameter), and recursively validate the generated objects. Exact-head hashes and CI census are recorded in [#1810](https://github.com/abiggerhammer/phil/issues/1810) and the parent audit receipts once complete.

## Native diagnostic regression, not a universal Haskell proof

The independent `test/P8F1RecursiveInverseMain.hs` uses strict GHC 9.6.7 `-Wall -Werror` and the **unchanged** real `P8SemanticFormCodec`, `SemanticForm`, `GenericApplicationIdentity`, `Data.Text.Encoding.encodeUtf8`, derived `Ord`, `Set` and `Map` for actual positive samples and rejecting negatives. It exercises deep nesting, empty/NUL/U+00E9/U+1F642/U+10FFFF, composed versus decomposed text, decimal boundaries, repeated members, noncanonical count, wrong typed D/V/Q/M roles, malformed UTF-8, truncation and trailing data. Finite native differential tests do **not** establish general GHC library operational correspondence.

## Remaining independent blockers

F1 proves **pure-model** universal inversion on the exactly stated D2-valid normalized structural domain, not total acceptance of arbitrary Haskell library objects or the accepted Phil source/release. There is no general native `Data.Text` / `Ord SemanticForm` / `Map` / `Set` correspondence proof, checked native↔Rocq accepted-object transport, or universally proved typed generic application inverse from this result. F2, if authorized to proceed by an actual F1 protected merge, must independently justify the native library bridge without inventing a new trust axiom. P9 final selected assurance, SYS-012/SYS-013, P8-C3 and P10 `FinalArtifactCertified` stay blocked. No signing, release or Phase 1 freeze is authorized.

This file documents a theorem statement, **not merge eligibility**: strict native/LLVM/conformance, all exact-head CI and reviews, ownership and protected merge intent must be verified separately.
