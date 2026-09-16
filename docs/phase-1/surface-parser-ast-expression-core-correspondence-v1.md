# Phase 1 surface parser AST expression-core correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #887.

The preceding converse-side slices established the outer source structure, declaration choice, type-alias shell, generic parameter/requirement structure, static-reference/static-value correspondence, and recursive type payload structure. The next shared dependency is ordinary `expression` syntax.

This slice closes the reusable non-command expression core:

- optional `or fail` / `or reject` fallback structure;
- shift, additive, and multiplicative precedence and left associativity;
- unary negation;
- named postfix expressions with static and term arguments;
- postfix projections;
- tuples and explicit parenthesization;
- Bool, Unit, Char, String, decimal-float, and decimal-integer leaves;
- exact failure-target references and recursively translated term arguments; and
- exact command-family identity at the `command_expression` boundary.

Production text literals and decimal floats use the existing closed `GrammarV1Expression` carrier. The production projection therefore maps the private Char/String carrier prefixes and decimal-point numeric spelling back to their distinct certified grammar leaf categories before comparison.

The first production consumers are the ordinary-expression holes previously left open by #887: indexed `Bytes[expression]` and the two expression payloads of `Validated[...]`, recursively through tuple/refinement base types. Bare `Bytes` is deliberately excluded on the production side when its source-unspellable runtime-length marker is present, matching the certified source tree's absence of an index expression.

## Evidence boundary

`command_expression` bodies are not translated in this slice. Their exact 27-way grammar alternative is preserved as a named opaque command-family node so command dispatch cannot collapse into ordinary syntax, but each command payload remains a successor obligation.

Likewise proposition bodies, session/effect payloads, and remaining declaration bodies remain open. Static references nested inside ordinary names/failure targets retain #883's static-argument payload boundary.

Accordingly `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted. Successor slices should translate propositions and command-expression payload families, then reuse those translations across the remaining declarations.
