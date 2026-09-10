# Phase 1 surface parser AST static-value correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #883.

The preceding converse-side slices established the outer source-file structure, declaration choice, the first `type_alias_decl` body shell, generic parameter/requirement structure, shallow type-constructor correspondence, and shallow `static_reference` correspondence. The next shared payload surface is `static_value_expression`.

## Scope

`Phil.Surface.GrammarV1.ReferenceAstStaticValue` projects both the extracted certified parse tree and the production `GrammarV1StaticValueExpression` AST to the same span-insensitive structural carrier.

The projection preserves:

- `true`, `false`, `unit`, and exact decimal-integer spelling;
- qualified static references through the #883 `static_reference` projection;
- explicit parentheses;
- postfix field projections;
- left-associative `+` and `-`;
- tighter left-associative `*`; and
- recursive production/reference tree shape for those constructs.

The type-alias consumer compares every root static-value argument carried by named-type, `Frame[...]`, and `Validated[...]` static references across the accepted surface corpus. Production convenience constructors (`GrammarV1StaticBoolArgument`, `GrammarV1StaticUnitArgument`, `GrammarV1StaticIntegerArgument`, and `GrammarV1StaticReferenceArgument`) are normalized back to the canonical grammar's single `static_value_expression` branch before comparison.

Direct controls reuse the existing SURF-002 expectations for arithmetic precedence/associativity, explicit grouping, projections, and primitive static-value leaves, and add qualified/Unicode reference cases plus a malformed-tree fail-closed control.

## Evidence boundary

This establishes structural correspondence for `static_value_expression` as consumed by type-alias root static arguments. Static references nested inside a static value continue to use #883's shallow static-argument category projection; session and effect-set static arguments remain category-only. Ordinary `expression`, `proposition`, deep type payloads, effect payloads, session payloads, and the remaining declaration families are not closed by this slice.

Accordingly `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested** and `PHIL-ASSURE-IMPL-CORR-001` is not promoted. Successor slices should close deep type payloads and proposition/expression/effect/session correspondence, then reuse those shared translators across the remaining declaration bodies.
