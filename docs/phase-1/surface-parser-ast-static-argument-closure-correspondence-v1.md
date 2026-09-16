# Grammar-v1 recursive static-argument AST correspondence

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #902 by replacing the shallow static-argument category boundary left by #883 with transitive payload checks.

For a production/certified `static_reference` pair, the closure checker first requires the existing static-reference spine correspondence to agree. It then enumerates every nested `static_argument` in preorder on both sides and checks each payload with the already-landed category-specific correspondence:

- `nonreference_type_expression` via the recursive type-payload correspondence;
- `nonreference_session_expression` via session correspondence;
- `static_value_expression` via structural static-value correspondence; and
- `effect_set_literal` via effect-set correspondence.

Production convenience carriers for bare static references, booleans, `unit`, and decimal integers are normalized back into the grammar's single static-value category before comparison, matching the abstraction established in #883/#885.

The production traversal follows nested static arguments transitively through types, ordinary expressions and command payloads, blocks, propositions, effects, sessions, and static values. Consequently a nested argument such as `Root[Config[1]]` cannot pass merely because both `1` and another value have the same shallow static-value tag; the inner argument is compared independently at its own occurrence.

Direct controls exercise primitive and recursive types, session arguments with boundary/proposition references, static arithmetic values, effect literals with term expressions, mixed type/proposition payloads, and ordinary command expressions containing static references. A same-shape nested static-value mismatch is required to fail closed.

This slice closes the deep static-argument payload seam across the existing correspondence surfaces. Remaining work is primarily the declaration-body layer needed to make certified-tree → production AST translation total over all 15 declaration families.

`PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested** until those declaration bodies are closed. This slice does not by itself promote `PHIL-ASSURE-IMPL-CORR-001` to Implementation Refined.
