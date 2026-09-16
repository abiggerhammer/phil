# Phase 1 surface parser AST-spine correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #872.

#871 mechanically bound production parse success to certified Grammar-v1 admission. #872 then exposed the certified `ParseTree` losslessly on the production side. The remaining converse/completeness problem is to show that every certified-valid tree can be translated into the specialized production syntax representation and that this translation agrees with the existing parser.

## First structural slice

This PR starts that translation at the outer Grammar-v1 spine:

```text
source_file = [ module_decl ], { import_decl }, { top_level_decl }
```

`Phil.Surface.GrammarV1.ReferenceAstSpine` consumes only the certified tree from #872. It validates the exact grammar-node structure for:

- `source_file`;
- optional `module_decl`;
- repeated `import_decl`;
- `qualified_name`;
- `identifier_list`; and
- the repeated `top_level_decl` segmentation.

It translates module and import information into the same span-insensitive production values used by `GrammarV1SourceFile`: qualified names and optional import selections. Top-level declaration bodies remain opaque in this slice, but every certified top-level entry must be structurally rooted at the canonical `top_level_decl` nonterminal and the certified count must equal the production AST count.

Source spans are intentionally ignored here. They are nonsemantic attachment data and are not represented in the proof-side `ParseTree`; the correspondence target is therefore production syntax modulo span attachment.

## Mechanical comparison

The dedicated Haskell gate parses each positive production-corpus fixture in two ways:

1. canonical pre-normalization source tokens → certified reference tree → certified source-file spine;
2. ordinary production parser → `GrammarV1SourceFile` → production source-file spine.

The two spine values must be exactly equal.

Direct controls include a source with:

- a dotted module name;
- an unselected import;
- a selected import with multiple identifiers; and
- a top-level declaration;

plus a bare-`Bytes` source to keep the pre-normalization boundary under pressure.

## Evidence boundary

This is real converse-side structural correspondence, but it is not yet complete parser equivalence. In particular, declaration bodies are not yet translated from certified grammar trees into the specialized production declaration AST.

Therefore:

- `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**;
- `PHIL-ASSURE-IMPL-CORR-001` remains unpromoted; and
- the successor descends through `top_level_decl`, attributes, and the declaration alternatives, then continues family-by-family until the certified-tree translation is total for every Grammar-v1 production.
