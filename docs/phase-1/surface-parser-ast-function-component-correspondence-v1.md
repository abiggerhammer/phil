# Phase 1 surface parser AST function/component correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after the callable-contract declaration body correspondence.

It relates certified Grammar-v1 parse trees to the production AST for `function_decl` and `component_decl`.

For functions, the projection preserves:

- optional `recursive` exactly as a Boolean declaration property;
- exact function name;
- ordered generic parameters and generic requirements;
- ordered mandatory term parameters;
- omitted versus present result type;
- mandatory `satisfies` type; and
- exact block structure via the previously landed block correspondence layer.

For components, the projection preserves:

- exact component name;
- ordered generic parameters and generic requirements;
- omitted versus explicit-empty versus populated optional term parameters;
- omitted versus present `provides` type; and
- exact block structure.

Nested type payloads reuse the recursive type correspondence; nested blocks reuse the block/statement correspondence and the recursive command-closure authority. Static references reached through those payloads remain covered by the deep static-argument closure gate.

The dedicated harness compares the certified recognizer tree with the production parser on minimal, rich, recursive, command-bearing, Unicode, explicit-empty, mixed-declaration, and adversarial mismatch controls, then runs the same comparison over every accepted parser-corpus fixture.

## Evidence boundary

After this slice, twelve of fifteen declaration families have direct body correspondence. The remaining declaration families are `protocol_decl`, `architecture_decl`, and `program_decl`.

This remains test-backed correspondence evidence. `PHIL-SURFACE-GRAMMAR-CORR-001` stays **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted until certified-tree to production-AST correspondence is total and the required production/refinement connection is complete.
