# Phase 1 surface parser AST generic-requirement correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #879.

#879 established exact ordered `generic_params` / `generic_param` correspondence for the `type_alias_decl` consumer, including all nine `generic_kind` alternatives. This slice closes the next shared declaration payload surface:

```text
generic_requirements = "requires", "{", { generic_requirement }, "}" ;
generic_requirement =
    "structural", identifier, ":", identifier, ";"
  | "proposition", proposition, ";"
  | "provider", identifier, ":", type_expression, ";"
  | "callable", identifier, ":", type_expression, ";"
  | "boundary", identifier, ":", type_expression, ";"
  | "architecture", identifier, ":", type_expression, ";"
  | "effects", identifier, "within", effect_set_expression, ";"
  | "authority", type_expression, ";"
  | "boundary", "representation", type_expression, ";"
  | "representation", proposition, ";"
  | "placement", proposition, ";"
  | "cost", proposition, ";"
  | "environment", proposition, ";"
  ;
```

## Certified requirement projection

`Phil.Surface.GrammarV1.ReferenceAstGenericRequirements` consumes only the certified parse tree exposed by #872. It validates the exact optional/list structure of the `type_alias_decl` requirement slot and the exact alternative index and delimiter/nonterminal structure of all thirteen `generic_requirement` productions.

The span-insensitive correspondence value preserves the payloads that are already closed by earlier slices:

- both identifier payloads of `structural` requirements;
- the identifier and shallow type-expression tag for provider/callable/boundary/architecture requirements;
- the identifier plus literal-vs-reference choice for effect-set requirements;
- the shallow type-expression tag for authority and boundary-representation requirements; and
- the distinct constructor category for proposition/representation/placement/cost/environment requirements.

Type payloads reuse #878's single type-constructor/spelling correspondence rather than defining a second interpretation.

Proposition bodies and the contents of effect-set literals/static references are deliberately not decoded here. Their canonical nonterminal/alternative shape is checked, but payload equality belongs to the later proposition/effect/reference correspondence slices.

## Mechanical comparison

The dedicated Haskell gate compares, for every accepted Phase 1 surface-corpus fixture containing a type alias:

1. canonical source tokens → certified reference tree → generic-requirement projection; and
2. ordinary production parser → `GrammarV1TypeAliasDecl` → the same span-insensitive projection.

The two values must be exactly equal.

Direct controls additionally require:

- absence of a `requires` block to map to an empty requirement list;
- one source fixture containing all thirteen requirement alternatives in canonical order;
- exact preservation of structural/named payload identifiers and representative type spellings; and
- both `effect_set_expression` branches: a literal set and a static-reference set.

## Evidence boundary

This closes the generic-requirement constructor/category surface for the first declaration-body consumer, including the simple payloads already supported by earlier correspondence slices. It does **not** yet establish deep equality for proposition bodies, static references, effect expressions, or nested type-expression payloads, and it does not yet translate the remaining declaration families.

Therefore:

- `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**;
- `PHIL-ASSURE-IMPL-CORR-001` remains unpromoted; and
- successor slices should close shared static-reference/type payloads and proposition/expression/effect syntax, then reuse those translations across the remaining declaration bodies until certified-tree → production AST correspondence is total.
