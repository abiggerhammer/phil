# Grammar-v1 block-command AST correspondence

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #899 by closing the seven command-expression wrappers that share the block/match substrate introduced there.

The production-side projection and certified-tree decoder cover:

- `borrow`, including owner expression, binder, and body;
- `if`, including full condition expression, optional join clause, then block, and optional else block;
- `match`, including full scrutinee, optional join clause, and ordered match arms;
- `decide`, including base scrutinee and ordered match arms;
- `closure`, including optional structural mode, ordered term parameters, satisfies type, optional captures, and body;
- `loop`, including state bindings, optional invariant, and body; and
- `offer`, including base scrutinee and ordered match arms.

The wrappers reuse #899 for block, statement, pattern, match-arm, join-clause, and loop-state structure; #889 for ordinary expression projections; #891 for propositions; and #887 for recursive type payloads.

Production normalizes omitted loop state and explicit `state ()` to the same empty state-binding list. This slice mirrors that existing AST normalization. Closure captures remain distinct between omission (`Nothing`) and explicit `captures ()` (`Just []`) because the production AST preserves that distinction.

Nested command expressions appearing inside blocks still pass through #889's explicit command-family tag boundary. Thus this slice closes the seven outer command wrappers, but it does not yet remove the remaining mutually recursive expression/type/static-argument integration seams.

After this slice, all 27 `command_expression` alternatives have direct certified-tree/production-AST payload correspondence at their own wrapper level. Remaining work is deeper mutual-recursion integration plus the declaration-body families needed to make certified-tree → production AST translation total.

`PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**. This slice does not by itself justify promoting `PHIL-ASSURE-IMPL-CORR-001` to Implementation Refined.
