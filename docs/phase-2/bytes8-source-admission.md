# PH2-S00-L0-E1 Bytes[8] source admission

[#1994](https://github.com/abiggerhammer/phil/issues/1994) allocates one
experimental source-only PR. The original `loan.phil` fixture is the exact
issue witness with LF endings and a trailing LF. The separately selected
`loan-escape.phil` control changes only `unit;` to `view;`.

## Selection and provenance

The selector is closed over these two origins. Its pins come from the issue
witness and the separately specified diagnostic control. Reviewers must compare
the pinned bytes and metadata with those external selections. Neither a
submitted `SourceOrigin` nor its digest can add an origin. The producer compares
the actual bytes directly to the selected bytes, hashes the actual UTF-8 input
with SHA-256, and compares the claimed path, declaration key, occurrence and
revisions to the fixed pin. The path is a logical repository file ID supplied
to the parser. The API processes supplied bytes and does not open a file.

| Selection | File under `test/phase2/s00/fixtures/` | Declaration key | SHA-256 |
| --- | --- | --- | --- |
| Original | `loan.phil` | `decl.phase2.s00.l0.e1.loan` | `02732835529e2b4de7a3dec878c6bf8e5532e7f587fbaa85eac79e4405b5de0a` |
| Escape control | `loan-escape.phil` | `decl.phase2.s00.l0.e1.escape-control` | `9224b9580607f977b9cc6780503a2e49b235e5eba9ec61d0364aa820308c8c20` |

Both pins identify the sole top-level `fn loan` at parser span `[0, 104)`.
These are zero-based Unicode code-point offsets with an exclusive end. The
production parser includes the trailing LF in the declaration span for these
fixtures. The byte comparison includes the LF independently of parser offsets.
The original returned value occurrence spans `[95, 100)`. The Grammar-v1
EBNF blob is `933fa282487eeae6ba224d68a8d49b9691c4e1dd` and the production
structural parser blob is `70aabbf9ea95271b1ed6852dfe5ace049bbda959`.
The hosted replay checks both against the working files. The declaration's
experimental interface and definition revisions use the existing identity
derivation with a dedicated interface tag and the exact original source in the
definition. The interface records `C` as an unresolved reference.

## Body result and contract STOP

The producer runs the production whole-file Grammar-v1 parser and requires
one closed function declaration with the exact nongeneric `Bytes[8]` header.
The bounded production adapter checks both types' Linear modes and resolves
the borrow and return to the exact parameter binder. The producer checks parity
with the production trace and requires the sole Linear owner before the loan,
the active loan during the borrow, the close with owner restored, and the
terminal consuming return. The private `CheckedBody` carries the original
declaration and return occurrences, owner and view binders, and the five
production checkpoints. Its public observation is a copyable report.
An independently selected escape produces `BorrowEscape` with the production
detail `shared view escapes its lexical scope`.

Calling `requireContractAuthority` with sealed body evidence always returns
`UnresolvedContractAuthority` for the selected declaration and its `C` reference.
The source contains no declaration of `C`. The producer exposes no route for a
caller to supply a revision, environment, instance, hash, proof claim, or
success flag as contract authority. The success type is `Void`. A contract
review would need a competent independent declaration and interface revision,
the actual applicable instance if required, and evidence for the exact
obligation bound to this function and source. Until then callable or emit
authorization stops here.

The seal is a Haskell module abstraction under ordinary typed use. It assumes
the reviewed producer and production dependencies were built from the
recorded checkout. It supplies no protection against modified binaries or
unsafe host primitives. This experiment yields body evidence only. Core,
Systems, LLVM, executable behavior, and final authority require separate
allocations and review.

## Replay

Run the three suites from the repository root with GHC 9.6.7. The hosted
workflow checks out the exact PR head, logs input identities, and verifies a
positive imported client plus separate compiler rejections for constructor
forgery, record update, report upgrade, and a fabricated contract submission.

```bash
cabal build lib:phil-core --only-dependencies
for test in test/phase2/s00/Bytes8SourceMain.hs \
  test/Phase1FSEM01BorrowResourceMain.hs test/Phase1FSEM01BorrowResourceTraceMain.hs
do
  cabal exec -- runghc -isrc -Wall -Werror "$test"
done
```

The experimental module is loaded from `src` by the focused test, with
dependencies already declared by the library. Existing package registration
and normative tests require no edits. Exact-head observations belong in the
draft PR evidence because this document is itself part of that head.
