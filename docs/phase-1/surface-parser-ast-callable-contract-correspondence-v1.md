# Phase 1 Grammar-v1 callable-contract AST correspondence

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` by relating certified `callable_contract_decl` parse trees to the production `GrammarV1CallableContractDecl` AST.

The correspondence preserves:

- callable name;
- ordered generic parameters and generic requirements;
- ordered term parameters and recursive parameter types;
- result type;
- ordered callable clauses; and
- the complete payload structure of all twelve `callable_clause` alternatives.

The clause projection covers `requires`, `consumes`, `borrows`, `authority`, `effects`, `outcomes`, `outcome`, `ensures`, `obligation`, `assumes`, `cost`, and `callee`. Nested outcome structure preserves all four outcome kinds, state-slot lists, callee preserve/consume/replace transitions, optional replacement state, ensures clauses, and obligation clauses.

Name sets preserve qualified-name segmentation and order. Type, proposition, effect-set, expression, and static-reference payloads reuse their previously landed correspondence layers. #902 remains the recursive command-closure authority for command expressions reached through cost/replacement-state payloads, and #903 remains the deep static-argument closure authority for nested references.

The dedicated gate compares certified and production projections for minimal and rich direct controls, all twelve callable clauses, all four outcome kinds, all residue-clause alternatives, all callee-transition alternatives, explicit empty collection forms, Unicode identifiers, mixed declarations, an adversarial replacement-state mismatch, and every accepted parser-corpus fixture.

## Evidence boundary

This closes `callable_contract_decl` only. After the provider-family slice, the remaining declaration bodies are `function_decl`, `protocol_decl`, `component_decl`, `architecture_decl`, and `program_decl`.

`PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**. `PHIL-ASSURE-IMPL-CORR-001` is not promoted to Implementation Refined by this evidence alone.
