# P8-E2 finite structural canonical-acceptance and typed GenericApplication model

Authorization: https://github.com/abiggerhammer/phil/issues/1770#issuecomment-6893306835 . This is the second and final allocated PR in the NEW P8-E two-PR budget; E1 #1798 has a verified protected merge. The historical P8-D 2/2 budget is exhausted and the independent P8-C3 unused slot is still STOPPED on P9 and shared-file authorization.

## Executable Rocq objects and intentionally bounded claims

This module **does not claim universal E1 decoder completeness or full model decode(encode(x))=x**. Its new executable canonical-acceptance function composes the actual E1 structural parser and encoder and D2 strict finite canonical structural predicate, rejecting all byte input that fails to re-encode to exactly the original bytes. The soundness theorem is universally quantified over every returned value and byte input, not an arbitrary caller-supplied proposition. It establishes that a *successful* normalization:
- consumed the whole wire via the E1 decoder,
- has D2-valid UTF-8 atoms and keys, strictly pairwise-ascending unique Set members and record keys,
- re-encodes to **exactly** the original bytes with canonical framing.

The converse theorem characterizes successful normalization exactly against the *actual executable* E1 parse, D2 validity check and encoder byte equality. It is not falsely promoted to the unproved statement that every D2-valid recursively nested structure always decodes from its emitted wire.

The second half defines a new executable diagnostic typed GenericApplication model over the existing D2 application record, with explicit **g D text V text count : (Q text M form)*** tags, strict E1 UTF-8 text and recursively parsed E1 semantic forms. Q argument count is parsed precisely and the decoded application must pass the *actual D2 strict key and full recursive value validation*. Its accepting full-wire parser additionally checks re-encoding byte-for-byte, so it does not normalize malformed keys/roles, counts, UTF-8, trailing bytes or noncanonical input.

Named proofs are:
- `p8_e2_bytes_equal_sound` / `p8_e2_bytes_equal_refl`: executable octet equality soundness and reflexivity;
- `p8_e2_normalized_form_sound` / `p8_e2_normalized_form_exact_characterization`: accepted structural bytes are exact canonical re-encodings, with strict recursive D2 validity;
- `p8_e2_expect_sound` / `p8_e2_argument_roles_are_exact`: successful parsing actually consumed the distinct Q and M role bytes;
- `p8_e2_argument_count_is_exact`: for **every** successfully parsed argument list, declared count equals the structurally returned number of fields;
- `p8_e2_parsed_application_is_valid` / `p8_e2_canonical_application_sound`: the model accepts only valid typed applications with exact full-wire canonical re-encoding;
- `p8_e2_wrong_application_role_rejected` / `p8_e2_wrong_argument_role_rejected`: universally quantified forbidden-tag behavior.

These are proposed mathematical properties to be credited ONLY if the hosted Rocq 9.2.0 compiler, named Print Assumptions and recursive `rocq check` succeed without Axiom/Admitted. Executable byte examples include empty application, nonempty typed argument, D/V role swaps, duplicate Q, unconsumed trailing bytes and the real constructor Ord/wire-tag reversal.

## Independent native source differential

Strict GHC 9.6.7 `-Wall -Werror` compiles and executes `test/P8E2CanonicalApplicationMain.hs` directly against the *read-only actual* `Phil.Core.Static`, `Phil.Core.Generic`, `P8SemanticFormCodec`, `Data.Text`, `Data.Text.Encoding`, `Map`, `Set` and derived native `Ord`. It checks recursive native roundtrips, typed GenericApplication D/V/Q/M roles (including identical text bytes in different typed roles), Unicode byte lengths and canonical map/set iteration, invalid counts, role swaps, duplicate/misordered keys, trailing and truncated bytes, nested invalid UTF-8, plus source-to-final native regressions. These tests are evidence of actual samples, not a universally quantified theorem about the foreign native libraries.

## Exact remaining proof gap — no premature P8 closure

The independently executable E1 recursive parser's **general count-decimal inversion and fuel/depth/recursive whole-domain roundtrip proof** is not completed by this E2 slice. It therefore cannot establish universal structural encoder injectivity or normalization of *every* D2-valid finite form, nor prove universal Haskell `Data.Text`, native derived `Ord`, `Map`/`Set`, GHC byte encoding, or actual production accepted-object correspondence to Rocq. Establishing that bridge would need a separately reviewed semantics relation/proof rather than a new trusted foreign-library axiom or a narrowed Phil accepted domain. E2's typed GenericApplication source identities are **actual UTF-8 byte sequences**, not fabricated natural-number IDs. Its proof is on model objects, **not P9 admission or final P7 source-event authority**.

Only NEW dedicated E2 proof, native test, doc and unprivileged workflow paths change. No existing C/D/E1 proof, production codec, Static/Generic/assurance, P9, Cabal/FSEM, Rocq grammar, TCB, normative 244 conformance cases, signed assets, privileged workflows or P11 are edited. After E2's protected merge or a fundamental proof blocker, P8-E must stop/disable; there is no third E PR. P8-C3, P9 SYS-012/013, P10 FinalArtifactCertified, signing and Phase 1 freeze remain BLOCKED.
