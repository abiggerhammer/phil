# Grammar-v1 reference-kernel bridge

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #867.

## Landed predecessor

#867 established a fresh Rocq 9.2 → Haskell extraction path for the exact certified Grammar-v1 reference recognizer composed with `phase1_surface_parser_total_fuel`. Its exact green head was `2bc8a8905774c9d11b4c76a1b0b98e0e1c7bc682`; it merged as `3bd77cccca458d2a6222a417c9d665268cc36d10`.

The green extracted `SurfaceGrammarRecognizerKernel.hs` artifact has SHA-256:

`fe9ae9159c61e2cb2fe5054b8e068a4fdfbd7be2bf9644f90f22bf1605329ff2`

The bridge workflow fresh-extracts the kernel and requires byte identity with that artifact before exercising the Haskell adapter.

## Representation bridge

#865 already projects the production lexer’s exact pre-normalization source-token stream to the proof-side token shape:

- grammar literals → `TLiteral`;
- lexical classes → `TLexical class lexeme`.

The extracted Rocq carrier represents `string` as a list of eight-bit `Ascii` constructors. Production source uses Unicode `Text`. `ReferenceKernelBridge.hs` therefore does not assert a false representation equality. Instead it:

1. encodes every literal/class/lexeme `Text` value as UTF-8;
2. maps each byte to the extracted `Ascii` constructor in Rocq’s least-significant-bit-first field order;
3. constructs the extracted `ConcreteToken` value;
4. invokes `phase1_surface_reference_accepts` from the freshly extracted kernel.

Grammar literal spellings and lexical-class names are ASCII. Lexical payloads are opaque to recognizer choice except for preservation in the parse result, so UTF-8 provides an injective byte representation at this acceptance boundary. A later parse-tree bridge must decode preserved payload bytes back to the production Unicode representation rather than silently reinterpreting them.

Bare `Bytes` remains on the #865 pre-normalization path: the production parser’s synthetic runtime-length marker is not presented to the reference recognizer.

## Mechanical pressure

The dedicated bridge workflow:

- re-derives the exact Grammar-v1 Rocq inputs from `grammar/phase1-surface.ebnf`;
- fresh-extracts `SurfaceGrammarRecognizerKernel.hs`;
- checks byte identity with the #867 green artifact;
- typechecks the generated kernel under `-Wall -Werror`, with only the documented extractor-owned `-Wname-shadowing` exception applied to a temporary compile copy;
- compiles the Haskell bridge and differential harness under ordinary `-Wall -Werror`;
- validates UTF-8 byte conversion on ASCII and multi-byte scalar examples;
- validates the repository’s complete manifest-driven surface corpus against both the existing production parser and the extracted reference recognizer.

## Evidence status

This is a staging correspondence slice. It gives the production lexer token stream an executable path into the certified reference recognizer and tests that path across the full finite production corpus, but it does not yet route production parser admission through the kernel and does not prove parse-tree/AST correspondence for every accepted source.

`PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**. `PHIL-ASSURE-IMPL-CORR-001` is not promoted by this slice.

The clean successor is the production-binding closeout: check in the exact extracted kernel, make the parser’s acceptance path fail closed through the certified recognizer, and then address completeness/parse-tree correspondence rather than treating an admission gate alone as language equality.
