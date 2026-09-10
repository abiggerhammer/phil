# Phase 1 surface parser reference-tree bridge v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #871.

#871 mechanically connected the public production parser to the certified Grammar-v1 recognizer in the soundness direction: production parse success cannot bypass certified rejection. The converse still needs a production path from every certified-valid parse to the specialized Grammar-v1 AST.

## Certified tree carrier

`GrammarDerivation.v` already defines a structural `ParseTree` that preserves:

- literal leaves;
- lexical-class leaves and their lexemes;
- named nonterminals;
- sequence structure;
- selected alternative indices;
- optional absence/presence; and
- repetition structure.

`GrammarParserProductionExtraction.v` already extracts `phase1_surface_reference_parse`, so no new proof-side parser or extraction entry point is introduced here.

`Phil.Surface.GrammarV1.ReferenceKernelBridge` now exposes a stable Haskell mirror, `GrammarV1ReferenceParseTree`, and losslessly decodes the extracted tree into production-facing values. Extracted Rocq strings are decoded under the same explicit UTF-8 contract introduced by #869; invalid byte sequences fail closed. Extracted natural-number alternative indices are converted structurally to `Integer`.

## Completeness precondition

For a canonical source-token stream, `grammarV1ReferenceParseSourceTokens` accepts only the exact complete reference result:

- extraction must return `Just`;
- the unconsumed token suffix must be empty;
- the result must be a single `ResultTree`, not `ResultTrees`; and
- every extracted string must satisfy the UTF-8 bridge contract.

The decoded tree can be flattened with `grammarV1ReferenceParseTreeTokens`. Structural nodes contribute no tokens; literal and lexical leaves reconstruct the exact `GrammarV1ReferenceToken` sequence.

The dedicated corpus gate requires, for every accepted fixture, that:

1. the root is the canonical `source_file` nonterminal;
2. certified parsing succeeds; and
3. flattened certified leaves are exactly equal to the canonical pre-normalization source-token projection.

Syntax-negative fixtures must not produce a certified complete tree.

The gate also checks a Unicode identifier directly and verifies UTF-8 encode/decode round-trip. A bare `Bytes` source is parsed through the certified tree and its recovered leaves are checked not to contain the production-only synthetic runtime-length marker.

## Evidence boundary

This slice makes the certified parse tree available losslessly on the production side and proves its token-leaf preservation over the complete finite production corpus. It does **not** yet translate every certified tree into `GrammarV1SourceFile`, nor prove that the existing handwritten AST construction is total for every certified tree.

Therefore:

- `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**;
- #871 remains the mechanical production-admission soundness connection; and
- `PHIL-ASSURE-IMPL-CORR-001` is not promoted by this slice alone.

The successor is a total, grammar-structural translation from `GrammarV1ReferenceParseTree` to the specialized production syntax/AST representation (including the deliberate bare-`Bytes` normalization), followed by equivalence against the existing parser output where both are defined.
