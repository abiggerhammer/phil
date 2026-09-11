# Phase 1 surface parser AST type/claim correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #904 by closing the next two declaration bodies: `type_alias_decl` and `claim_decl`.

## Closed in this slice

For type aliases, the correspondence preserves:

- the exact declaration name;
- ordered optional generic parameters;
- ordered optional generic requirements; and
- the complete recursive target type payload through the existing type correspondence layer.

For claims, the correspondence preserves:

- the exact declaration name;
- ordered optional generic parameters and requirements;
- the distinction between omitted term parameters and an explicit empty `()` list;
- ordered named term parameters and recursive type payloads; and
- omitted versus present transparent proposition bodies, using the existing proposition correspondence layer.

A reusable `ReferenceAstTermParams` layer is introduced here so later callable, function, component, and related declaration slices can share the same certified-tree → production-AST term-parameter decoder.

The permanent gate exercises minimal, rich, Unicode, explicit-empty, mixed-declaration, and mismatched-payload controls and compares all accepted parser-corpus fixtures through the certified recognizer and production parser.

## Existing recursive guarantees

#902 continues to close recursively nested command correspondence. #903 continues to close deep static-argument payload correspondence. Consequently nested commands and static arguments reached through type/claim payloads remain covered by their dedicated gates rather than being reimplemented here.

## Remaining boundary

After #904 and this slice, four of the fifteen declaration bodies have direct correspondence: record, data, type alias, and claim. The remaining eleven declaration families are still open.

`PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**. `PHIL-ASSURE-IMPL-CORR-001` is not promoted to Implementation Refined by this slice.
