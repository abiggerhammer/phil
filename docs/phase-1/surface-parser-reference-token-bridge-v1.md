# Phase 1 surface parser reference-token bridge v1

This is the first production-correspondence slice after the finite Grammar-v1 reference recognizer was completed by #830.

It advances logic-ledger obligation `PHIL-SURFACE-GRAMMAR-CORR-001`. It does **not** yet claim whole-parser soundness or completeness.

## Boundary being closed

The Rocq reference recognizer consumes exactly two token forms from `GrammarDerivation.v`:

- `TLiteral literal`
- `TLexical class lexeme`

The production Haskell lexer historically exposed only its parser-facing `GrammarV1Token` carrier. Some source categories share that closed carrier through checked pattern synonyms, and `lexGrammarV1` additionally performs one production-only compatibility normalization: bare `Bytes` is expanded to an unspellable synthetic `Bytes[marker]` token sequence so the stable structural parser can reuse its indexed-Bytes path.

That parser normalization is not Grammar-v1 source syntax and therefore must not enter the proof-side token stream.

## This slice

`lexGrammarV1SourceTokens` now exposes the exact located source-token stream before production-only normalization. Existing `lexGrammarV1` behavior is unchanged: it applies `expandRuntimeBytes` to that canonical source stream before invoking the production parser.

`Phil.Surface.GrammarV1.ReferenceToken` defines a Haskell mirror of the proof-side two-constructor token carrier:

- `GrammarV1LiteralToken Text`
- `GrammarV1LexicalToken class lexeme`

The projection is exhaustive over the production token carrier and preserves exact Grammar-v1 classification:

- identifiers → `IDENTIFIER`
- decimal integers → `DECIMAL_INTEGER`
- decimal floats → `DECIMAL_FLOAT`
- string literals → `STRING_LITERAL`
- character literals → `CHAR_LITERAL`
- unsigned type tokens → `UINT_TYPE`
- signed type tokens → `SINT_TYPE`
- every quoted grammar keyword/operator, including `F32`, `F64`, `String`, `Char`, and `Bytes`, remains a literal token.

Decoded string/character lexemes and source spans are preserved by projection.

## Mechanical pressure

`Phase1GrammarV1ReferenceTokenMain.hs` derives both surfaces directly from `grammar/phase1-surface.ebnf`:

1. every `<LEXICAL_CLASS>` appearing in the normative productions must equal the seven classes handled by the bridge;
2. every quoted grammar literal must lex in isolation to exactly one reference literal token with the same spelling;
3. representative values for every lexical class must retain their exact decoded lexeme;
4. bare `Bytes` must remain one literal token on the canonical/reference side while the existing production parser path still receives its synthetic index marker;
5. explicit `Bytes[8]` must remain token-preserving through production normalization;
6. located source spans must be unchanged by the reference projection.

A dedicated CI workflow runs the bridge under GHC 9.6.7 with `-Wall -Werror`.

## What remains

This slice establishes the concrete token representation boundary only. The next correspondence work must connect the production parser's acceptance and structural result to the already-certified reference recognizer over these projected tokens.

Until that connection is mechanized, `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**. Unicode library behavior, source-byte/Text decoding, Megaparsec behavior, and the production structural parser itself remain explicit front-end correspondence boundaries.
