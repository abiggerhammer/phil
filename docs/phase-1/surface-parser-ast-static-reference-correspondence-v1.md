# Phase 1 surface parser AST static-reference correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #881.

The preceding converse-side slices established the outer source-file structure, top-level attributes/declaration choice, the first `type_alias_decl` body shell, shallow type-constructor correspondence, generic parameters, and all thirteen generic-requirement categories. A large fraction of the remaining nested syntax depends on one shared carrier:

```text
static_reference = qualified_name, [ static_arguments ] ;
static_arguments =
  "[", [ static_argument, { ",", static_argument } ], "]" ;
static_argument =
    nonreference_type_expression
  | nonreference_session_expression
  | static_value_expression
  | effect_set_literal
  ;
```

## Certified static-reference projection

`Phil.Surface.GrammarV1.ReferenceAstStaticReference` consumes only the certified parse tree exposed by the extracted reference recognizer. It validates:

- the exact two-field `static_reference` structure;
- the complete dotted `qualified_name` spelling;
- absence, empty presence, and nonempty `static_arguments`;
- comma-separated argument structure; and
- the exact alternative selected for each of the four `static_argument` grammar branches.

The type-argument branch reuses #878's shallow type-constructor/spelling projection, including the production parser's closed primitive spelling carrier.

## Production normalization boundary

The production AST deliberately has convenience constructors for simple static values:

- `GrammarV1StaticBoolArgument`;
- `GrammarV1StaticUnitArgument`;
- `GrammarV1StaticIntegerArgument`; and
- `GrammarV1StaticReferenceArgument`.

At the Grammar-v1 EBNF boundary, however, all four arise through the single `static_value_expression` branch of `static_argument`. This slice therefore maps those convenience constructors, together with `GrammarV1StaticValueArgument`, back to one `GrammarV1ReferenceStaticValueArgument` grammar-category tag.

That collapse is intentional and lossless for the claim made here: exact grammar-alternative correspondence. A successor static-value-expression slice must refine the payloads inside that category before full AST equivalence can be claimed.

Similarly, this slice records session and effect-set arguments at their grammar-category boundary; their nested payloads remain for dedicated successors.

## First production consumer

The full-corpus comparison uses `type_alias_decl` as the first consumer. It compares root static references carried by:

- named-type targets;
- `Frame[...]`; and
- the validator reference in `Validated[...]`.

Direct controls additionally exercise:

- a dotted reference with no static arguments;
- an explicitly empty static-argument list;
- all four static-argument grammar categories in one reference;
- a generic-name reference represented by the production convenience static-reference argument carrier;
- nested static arguments under `Frame`; and
- nested static arguments under `Validated`.

## Evidence boundary

This is reusable static-reference and static-argument-category correspondence, not deep static-argument equivalence. In particular, nested static values, sessions, effect contents, static-reference recursion inside static values, propositions, ordinary expressions, and deep type payloads remain open.

Therefore:

- `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**;
- `PHIL-ASSURE-IMPL-CORR-001` remains unpromoted; and
- successor slices refine static-value/session/effect payloads and then reuse those shared translations across the remaining declaration-family bodies.
