# Phase 1 surface parser AST generic-parameter correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #878.

#878 established the first declaration-body correspondence for `type_alias_decl` and an exhaustive shallow correspondence for the `type_expression` / `nonreference_type_expression` constructor surface. The next reusable declaration dependency is the generic parameter list.

## Grammar surface

The canonical Grammar-v1 forms are:

```text
generic_params = "[", generic_param, { ",", generic_param }, "]" ;
generic_param = identifier, ":", generic_kind ;
generic_kind =
    "Type"
  | "Nat"
  | "Session"
  | "Message"
  | "Effects"
  | "provider", type_expression
  | "callable", type_expression
  | "boundary", type_expression
  | "architecture", type_expression
  ;
```

`Phil.Surface.GrammarV1.ReferenceAstGenericParams` consumes the certified reference tree exposed by #872 and validates the exact optional/list/sequence structure used by `type_alias_decl`.

For each generic parameter it preserves the exact identifier and maps all nine `generic_kind` alternatives to a span-insensitive production-facing spine. The provider/callable/boundary/architecture kind payloads reuse #878's `GrammarV1ReferenceTypeTag` correspondence, so this slice does not create a second interpretation of type syntax.

## Mechanical comparison

The production projection reads `GrammarV1TypeAliasDecl` values and erases source spans while preserving:

- alias name;
- ordered generic parameter names; and
- each parameter's exact generic-kind constructor, including the shallow target-type tag for contract kinds.

The certified projection traverses the corresponding `type_alias_decl` parse tree and must produce exactly the same value.

The dedicated gate:

- checks the complete positive Phase 1 surface corpus;
- checks absence of generic parameters;
- checks a Unicode generic parameter name; and
- exercises all nine generic-kind alternatives in one direct source fixture, including contract-kind payloads with primitive, Bytes, and named types.

## Evidence boundary

This closes generic-parameter name/kind correspondence for the `type_alias_decl` consumer and provides a reusable decoder for later declaration-family slices. It does **not** yet establish deep correspondence for the type payloads nested under contract kinds; those remain at #878's constructor/spelling level. `generic_requirements`, expressions, propositions, sessions, and the remaining declaration bodies are also still open.

Therefore:

- `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**;
- `PHIL-ASSURE-IMPL-CORR-001` is not promoted; and
- successor slices should close `generic_requirements` and then descend shared nested type/reference/expression/proposition syntax so the declaration-family translations can reuse them.
