# P8-H9 — D2 structural order coherence (isolated Rocq preflight)

Controlling authorization: [#1904](https://github.com/abiggerhammer/phil/issues/1904); parent [#1770](https://github.com/abiggerhammer/phil/issues/1770); proof-tranche ledger [#1810](https://github.com/abiggerhammer/phil/issues/1810); audit [#1584](https://github.com/abiggerhammer/phil/issues/1584). H8 [#1894](https://github.com/abiggerhammer/phil/pull/1894) was already protected-merged. H9 is a **separate one-PR pure mathematical authorization**.

**Proof status: hosted scratch validation passed; official PR exact-head validation and protected merge are pending.** The actual D2 and H8 definitions are unchanged. Do not count any theorem until an exact-source hosted Rocq 9.2.0 workflow has compiled every object, printed closed assumptions, performed recursive `rocq check`, and recorded source and object receipts. Scratch preflight does not itself authorize a published PR.

## Precise mathematical scope

The H9 file works directly with the mutually inductive `P8D2Form`, `P8D2Forms`, `P8D2Fields` structures and the original `p8_d2_compare_form/forms/fields` functions, which compare **constructor rank Atom < Ordered < Unordered < Record** (not encoded wire tags). Record fields compare key octets first, then nested values, then the field-list tail. Each list uses lexicographic empty/prefix ordering.

The following universal results compiled successfully at scratch head `bcb197f1f0a42cc61fb2f9eea6dd07291a5f8366`; official PR-head checks are required before merge:

1. Original `p8_d2_compare_bytes`: common-prefix and proper-prefix laws, reflexivity, exact `Eq iff list equality`, comparison reversal and strict `Lt` transitivity.
2. Original mutually recursive form/forms/fields comparisons: reflexivity, `Eq` reflection to actual recursive constructor equality, comparison reversal, strict `Lt` transitivity, and exact trichotomy (equal or one of the two opposite strict comparison directions). These are proofs about every finite mathematical D2 term, so no bounded enumeration, assumed foreign comparator, or caller-supplied proof premise is involved.
3. New H9-local `p8_h9_adjacent_members` and `p8_h9_adjacent_keys` predicates, with both implication directions against original D2 *pairwise* `p8_d2_strict_members` and `p8_d2_strict_keys`. The original canonical-domain predicates remain unchanged. Strict transitivity is explicitly required to derive adjacent ⇒ pairwise; no deduplication or sorting of output is performed.
4. Application of H8's universal canonical Unicode scalar octet-order theorem to `P8D2Atom` ordering, **without** asserting anything about Haskell's native `Text` representation or derived `Ord`.

## Discriminating model witnesses

The H9-owned tests cover empty and prefix lists/fields; nested Ordered/Unordered/Record forms; constructor rank distinct from wire tag ordering; key-first versus value-first record comparisons, tied keys and distinct or equal values; sorted three-member and three-key sequences, reversed and duplicate member/key rejection; NFC versus NFD distinct octets; NUL; the scalar boundaries U+007F/U+0080, U+07FF/U+0800, U+D7FF/U+E000, U+FFFF/U+10000, and U+10FFFF. Overlong, surrogate and above-max byte sequences must be rejected by the unchanged D1/D2 validity model. These examples are regression witnesses, **not substitutes for universal theorems**.

## Authority and verification discipline

Only three new H9 paths are writable: this note, `proof/Phil/Verification/P8H9StructuralOrderCoherence.v`, and the dedicated unprivileged `phase1-p8-h9-structural-order.yml`. Upstream D2/H8, Haskell, GHC libraries, Cabal, grammar, 244 normative cases, signing, P9/FSEM, P11, privileged CI and the trusted computing base are read-only.

Scratch proof evidence: [Rocq 9.2.0 run #44461358202](https://github.com/abiggerhammer/phil/actions/runs/44461358202) completed SUCCESS on `bcb197f1f0a42cc61fb2f9eea6dd07291a5f8366`, including all five upstream/H9 `.vo` recursive checks and 68 named closed-assumption reports. H9 proof source SHA-256 `17d7f9c778079bad30574b246d53fef7c670b113a5467b155e0318c81e4d397a`, H9 `.vo` SHA-256 `2c19ed0ef2aea91d5d3f0fbba23cf607fde38ab8d394d363fe58df7ae1c2bb3d`, assumption transcript SHA-256 `5839f11a3e6b25e9c4da95dda3be73fc3c8d3ece2b29caedacae91f4a259fa82`. These are scratch-head receipts, not official PR evidence. 

The dedicated workflow must compile unchanged C1/D1/D2/H8 plus H9 using Rocq 9.2.0; reject `Axiom`, `Admitted`, `Parameter` and incomplete proofs; print named assumptions, `rocq check` each compiled object, and hash exact source/object/assumption output. Publication is permitted only after successful hosted proof checks and a fresh one-active-P8-PR census, followed by the normal exact-head protected merge gates. No native↔Rocq commuting theorem, `GHC.Text/Map/Set` operational law, selected-build attestation (#1826), foreign-library signoff (#1827), P8-F2/C3, P10, TCB approval or Phase 1 freeze follows from H9.

