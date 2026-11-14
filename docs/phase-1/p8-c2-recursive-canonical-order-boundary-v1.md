# P8-C2 — recursive native ordering and concrete canonical octet keys (PARTIAL)

Source pin: main f28d540cb113bfb2c7bebcfa54ed8df68b1d40cf (protected P8-C1 #1779 merge), 2026-11-14. Governing P8 #1770 comment 6875298118. This is the second PR of the NEW three-PR P8-C budget; P8-A/B earlier budgets are closed. P9 #1771 independently blocked; P10 #1772 blocked.

## Concrete native and Rocq results

Native Phil.Core.Static.SemanticForm derives Ord: Atom, Ordered, Unordered, Record are constructor variants; Text compares under real Data.Text Ord; ordered children compare lexicographically; Set/Map canonical trees compare using ascending members and keys. The existing P8SemanticFormCodec sorts actual typed native values using Set.toAscList and Map.toAscList and enforces strictly ascending keys on decode. Generic D/V/Q/M have distinct typed roles/wire tags even if their textual payloads coincide.

The new Haskell differential test implements an independent constructor/recursive comparator WITHOUT using Ord SemanticForm, and checks it against native deriving Ord across bounded Unicode, nested sets/maps/ordered forms. It tests native codec recursive round-trip and finite-domain injectivity, Unicode Text versus UTF-8 octet lexical order, Map/Set insertion order and duplicate normalization, malformed nesting/UTF-8, duplicate/reversed map/set/generic Q keys, and wrong-role substitution. These are finite executed tests, NOT universal Haskell-Rocq proofs.

Rocq P8RecursiveCanonicalOrderModel.v imports C1 single-scalar byte grammar. It defines a real byte-list lex comparison and executable canonical list predicate requiring each key be strictly smaller than EVERY later key. Theorem p8_c2_bytes_ltb_irrefl proves comparison irreflexivity; p8_c2_strict_keys_no_duplicates proves NoDup, *without an assumed abstract order or unproved transitivity premise*. A derived result verifies canonical record keys are unique. Constructor rank for four forms and role tags for D/V/Q/M are explicit. Canonical byte examples include U+00E9, singleton prefix, duplicates, reversal and C1 surrogate rejection. A concrete negative shows wire-byte order DOES NOT equal native Ord for all constructors: native Unordered < Record, but wire tag u > r. Sorting raw codec bytes would therefore be invalid.

A nonprivileged path-scoped workflow requires complete strict GHC 9.6.7 -Wall -Werror, native tests, C1 and accepted Upload/Steve StageClosure/release regressions; Rocq 9.2.0 compiled C1 dependency and C2 object, Print Assumptions, full recursive rocq check and checksums. No existing source/proof/TCB, release, FSEM, P9 SYS-012/013 or 244 normative cases changed.

## Unproved claims and stop boundaries

1. The Rocq model's canonical keys are byte sequences. It does NOT prove a full recursive structural native SemanticForm Ord equivalence across languages, valid concatenated UTF-8 Text streams, or a Haskell Data.Text operational-semantics proof. The native differential is sampled evidence.
2. Existing native recursive codec has executed roundtrips; a full Rocq recursive byte serializer/parser and universal roundtrip/injectivity theorem on the ACTUAL accepted Haskell SemanticForm domain, with canonical Map/Set shape, are NOT established. Model all-pairs byte key sortedness is not a substitute for a native producer.
3. Generic D/V/Q/M tags and native K/I source, independent R/L, S/C/F, B/I_stage/A/P, selected manifest, whole StageClosure, P7 release, LLVM/target/trust are not translated into a competent opaque Rocq accepting producer. No caller-supplied Prop, synthetic identity nat encoding, global acceptance or TCB expansion is asserted.
4. C3 must STOP if P9's source event provenance, complete SYS-012 consumer universe and selected immutable SYS-013 assumption authority cannot be attached to the actual P2/P6/P7 accepted whole object. P10 FinalArtifactCertified stays UNPROVED and Phase 1 is not frozen.

Merge only with exact-head hosted full GHC and Rocq 9.2 proof/check assumptions, all negatives, complete 100%-green CI census, no branch/file collisions or reviews, and protected merge intent. Successful C2 is partial, not P8 closure. P11 and independent external audit remain separate gates.
