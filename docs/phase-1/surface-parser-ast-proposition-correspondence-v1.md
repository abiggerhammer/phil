# Phase 1 surface parser AST proposition correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #889.

The proposition grammar is compact enough to close structurally as one shared layer. `Phil.Surface.GrammarV1.ReferenceAstProposition` consumes the certified reference tree and relates it to the span-insensitive production `GrammarV1Proposition` structure for:

- left-associated `or` and tighter `and`;
- recursive `not`;
- `true` and `false`;
- all eight relation operators (`==`, `!=`, `<=`, `>=`, `<`, `>`, `in`, `disjoint`);
- claim applications with exact static-reference identity and recursively translated term arguments; and
- parenthesized propositions, whose grouping effect is preserved by the resulting tree but whose wrapper is deliberately erased because the production AST has no parenthesized-proposition constructor.

Relation operands and claim arguments reuse #889's ordinary-expression correspondence. Static references reuse #883's correspondence boundary.

## Production completeness repair

The converse pass found a real handwritten-parser mismatch. Grammar v1 defines:

`relation_proposition = shift_expression, relation_operator, shift_expression`

but the production parser was consuming `additive_expression` on both sides of a relation. That made certified-valid sources such as `a << 1 == b >> 2` vulnerable to production rejection. This slice changes both relation operands to `parseShiftExpression` and includes that exact shifted-relation form as a permanent regression control.

## First production consumers

The full-corpus gate compares proposition payloads already exposed by earlier type-alias correspondence slices:

- `proposition`, `representation`, `placement`, `cost`, and `environment` generic requirements;
- `Proof[P]`; and
- refinement propositions, recursively through tuple/refinement base types.

This turns the proposition holes left by #881/#887 into structural correspondence for those consumers without claiming that every remaining declaration body is translated.

## Evidence boundary

The expression nodes embedded in relations and claim applications inherit #889's explicit command-expression boundary: ordinary expression structure is translated, but the 27 command-expression payload bodies are still opaque. Session/effect payloads and the remaining declaration families are also still open.

Accordingly `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted. Successor slices should close command-expression payloads and session/effect structure, then reuse the shared translators across the remaining declaration bodies.
