# Phase 1 Grammar-v1 architecture/program declaration correspondence

This slice extends `PHIL-SURFACE-GRAMMAR-CORR-001` from the thirteen declaration families closed through #912 to the final two declaration families: `architecture_decl` and `program_decl`.

The architecture correspondence preserves the exact architecture name, ordered generic parameters and requirements, and every ordered `architecture_item` alternative: instance/static-reference creation, qualified references and process targets, protocol occurrences, internal versus explicit-external role targets, bindings, authority origins, grant expressions, boundary bindings, entry types, scoped assumptions, exported obligations, observables, and constraints.

The program correspondence preserves the exact program name and instantiated static reference, distinguishes an omitted program block from a present block whose item sequence may be empty, and preserves all four ordered `program_item` alternatives: entry types, scoped assumptions, exported obligations, and observables.

Nested generic, type, proposition, expression, and static-reference payloads reuse the correspondence layers already landed in the preceding tranche. In particular, #902 remains the recursive command-closure authority for command-bearing expression payloads and #903 remains the deep static-argument closure authority.

The permanent gate includes minimal, all-item, static-reference, Unicode, mixed-declaration, and adversarial payload controls, then compares every accepted parser-corpus fixture through both the certified recognizer tree and the production parser AST.

After this slice, all 15 Grammar-v1 declaration families have direct body correspondence. This closes the declaration-body coverage required before the final cumulative certified-tree → production-AST correspondence closeout can audit the total translation boundary.

This remains **Active / Tested** evidence for `PHIL-SURFACE-GRAMMAR-CORR-001` until that cumulative closeout lands. It does not by itself promote `PHIL-ASSURE-IMPL-CORR-001` to Implementation Refined.
