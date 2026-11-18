# P8-H9 — initial structural-order mathematical preflight

Authority: [P8-H9 #1904](https://github.com/abiggerhammer/phil/issues/1904), parent [P8 #1770](https://github.com/abiggerhammer/phil/issues/1770), original proof tranche [#1810](https://github.com/abiggerhammer/phil/issues/1810); completed H8 [#1894](https://github.com/abiggerhammer/phil/pull/1894).

**Status: SCRATCH-ONLY FIRST PRECURSOR; NOT THE H9 COMPLETION CRITERION OR OFFICIAL PR.** Do not present these statements as proved until their exact-source hosted Rocq 9.2 checks pass. No native `Text`, `Ord SemanticForm`, `Set`, `Map`, foreign T1–T4, full Haskell-to-Rocq relation, P8-F2, P8-C3, P10 or release certification is established.

## What this first precursor attempts

With the existing D2 model kept byte-identical, the new proof-local module introduces:

- Exact common-byte-prefix preservation of `p8_d2_compare_bytes`.
- A proper byte prefix compares strictly less than any nonempty extension.
- New **adjacent** predicates for `P8D2Forms` and `P8D2Fields` without modifying original `p8_d2_strict_members` and `p8_d2_strict_keys`.
- The easy universally quantified direction: original **pairwise strict** normalization implies adjacent strict normalization.
- Smoke examples for empty members, duplicate members and reversed record keys.

The important **missing reverse direction** requires a substantive proof of transitivity for the *actual mutually recursive D2 comparator*, not a presumed Haskell foreign `Ord` law. It is intentionally not assumed. Full H9 still needs comparison reflexivity, equality reflection and order coherence for all finite D2 forms/lists/fields, and then both adjacent↔pairwise strict theorems, with nested and Unicode examples.

## Scratch verification boundary

The dedicated unprivileged workflow compiles unchanged C1/D1/D2/H8 and this candidate H9 preflight, checks all proof objects recursively and prints assumptions. This document and source are intentionally on the scratch branch until the complete H9 theorem set, exact-head evidence and one-PR lane gate are satisfied. No change to the 244 normative cases, upstream P8 files, Haskell, grammar, Cabal, privileged CI or TCB.
