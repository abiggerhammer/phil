# Phase 1 surface parser production binding v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #869.

## Production admission boundary

`parseGrammarV1StructuralSource` now lexes exactly once with
`lexGrammarV1SourceTokens`.  The resulting canonical, pre-normalization token
stream is passed to `grammarV1ReferenceAcceptsSourceTokens`, which maps the
production tokens through the #865 reference-token projection and the #869
UTF-8 byte bridge into the extracted certified recognizer.

If the certified recognizer rejects, the public parser returns
`GrammarV1CertifiedGrammarDiagnostic` and the handwritten structural parser is
not run.  Only certified-accepted source tokens are then transformed by
`grammarV1ParserTokensFromSourceTokens`, which applies the existing
production-only bare-`Bytes` compatibility normalization, and passed to the
handwritten structural parser.

This ordering keeps the synthetic bare-`Bytes` marker outside the normative
Grammar-v1 token stream while avoiding a second lexer pass.

## Extracted kernel identity

`generated/SurfaceGrammarRecognizerKernel.hs` is the exact Rocq 9.2 extraction
staged in #867.  Its SHA-256 is:

`bd1bfb3cf517fe09bdaa9dbf5ceb034780e280488baf1cbc97a34ee5a8a2d19f`

`src/SurfaceGrammarRecognizerKernel.hs` is the production compile mirror: one
module-local `-Wno-name-shadowing` pragma, followed byte-for-byte by the exact
extracted kernel.  The exception is limited to the two extractor-generated
nested helper bindings identified during #867; every other GHC warning remains
fatal.

The production-binding workflow fresh-extracts the recognizer from the
normative grammar and proof sources, checks the pinned hash, compares it
byte-for-byte to `generated/SurfaceGrammarRecognizerKernel.hs`, and checks that
the production mirror has no other changes.

## Mechanical dependency test

The ordinary corpus test exercises the real checked-in certified kernel.
Additionally, `test/fakes/SurfaceGrammarRecognizerKernel.hs` implements the
same narrow carrier API but rejects every token stream.  The dedicated binding
test temporarily removes the real kernel from the source path and compiles the
public production parser against that rejecting test double.  A source program
that the handwritten parser ordinarily accepts must then return
`GrammarV1CertifiedGrammarDiagnostic`.

This is a direct control that production success depends on the certified
decision rather than merely agreeing with it on a finite corpus.

## Evidence boundary

This slice establishes a mechanical **production soundness / admission**
connection: a successful public Grammar-v1 production parse can occur only
after the certified reference recognizer accepts the exact source token stream.
Because #830 proves that recognizer sound for the normative Grammar-v1
semantics, the handwritten parser can no longer admit syntax outside that
language.

It does **not** establish the converse.  The handwritten structural parser may
still reject a source token stream accepted by the certified recognizer, and no
general translation theorem yet relates every certified reference parse tree
to the specialized `GrammarV1SourceFile` AST.  Those completeness and
parse-tree/AST correspondence obligations remain the successor work.

Therefore `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested** after this
slice, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted to Implementation
Refined solely from this admission binding.
