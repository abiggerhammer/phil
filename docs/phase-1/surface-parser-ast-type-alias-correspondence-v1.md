# Phase 1 surface parser AST type-alias correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #876.

#876 established exact correspondence for ordered top-level attributes and the exhaustive fifteen-way `declaration` choice. Declaration bodies remained opaque.

This slice begins declaration-body correspondence with `type_alias_decl` while also establishing a reusable shallow correspondence for the shared `type_expression` constructor surface.

## Type-alias shell

The certified tree decoder validates the exact Grammar-v1 shape:

```text
type_alias_decl =
  "type", identifier, [ generic_params ], [ generic_requirements ],
  "=", type_expression, ";" ;
```

It projects the same span-insensitive information carried by the production `GrammarV1TypeAliasDecl`:

- alias name;
- generic-parameter count;
- generic-requirement count; and
- target type constructor/spelling tag.

The optional generic-parameter and generic-requirement nodes are structurally validated before their counts are accepted. Their internal kind/requirement payload correspondence remains a later shared-syntax slice.

## Shared type-expression constructor spine

The certified decoder exhaustively distinguishes the two `type_expression` alternatives and all thirteen `nonreference_type_expression` alternatives.

The production parser intentionally uses one closed primitive spelling carrier, `GrammarV1UnsignedType Text`, for `Char`, `String`, U-width integers, I-width integers, and F32/F64. Accordingly the correspondence target preserves exact primitive spelling rather than inventing new production constructors.

The shallow target categories are:

- Unit;
- Bool;
- exact primitive spelling (`Char`, `String`, `U<n>`, `I<n>`, `F32`, `F64`);
- Bytes;
- Frame;
- Proof;
- Validated;
- refinement type;
- tuple type; and
- named type.

Compound alternatives validate their required delimiter/nonterminal shape but do not yet translate nested payload ASTs. In particular, bare `Bytes` and indexed `Bytes[n]` both correspond to the production `GrammarV1BytesType` constructor here; the deliberate production-only runtime-length marker remains below this slice's abstraction boundary.

## Mechanical checks

The dedicated gate compares every type alias in every accepted Phase 1 surface-corpus fixture through two paths:

1. canonical source tokens → certified reference tree → certified type-alias/type-constructor spine;
2. ordinary production parser → `GrammarV1TypeAliasDecl` → production spine.

The projections must be exactly equal.

Direct controls separately exercise Unit, Bool, Char, String, U32, I32, F32, F64, bare Bytes, indexed Bytes, Frame, Proof, Validated, refinement, tuple, and named targets, plus a generic alias with two generic parameters and one generic requirement.

## Evidence boundary

This is not complete `type_alias_decl` AST correspondence. Generic parameter/requirement payloads and nested type-expression payloads remain to be translated, and the other fourteen declaration families remain open.

Therefore `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted. Successor slices can now descend shared generic/type payload syntax and reuse that machinery across the remaining declaration families.
