# Phase 1 surface parser AST provider-declaration correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #907 by closing the three provider declaration families:

- `provider_contract_decl`;
- `provider_implementation_decl`; and
- `opaque_provider_implementation_decl`.

## Closed in this slice

The certified Grammar-v1 parse tree is related directly to the production AST for:

- exact provider names;
- ordered generic parameters and generic requirements through the declaration-common correspondence layer;
- provider-contract operations with exact recursive type payloads;
- provider-contract laws and lifecycle clauses with exact proposition payloads;
- provider-implementation `satisfies` types;
- provider-implementation operations with exact names, recursive type payloads, and block structure;
- provider-implementation laws and lifecycle clauses; and
- opaque provider-implementation target types and terminator shape.

The dedicated harness exercises empty and rich declarations for all three families, all six contract/implementation item alternatives, Unicode identifiers, mixed-source declaration ordering, an adversarial operation-type mismatch, and every accepted parser-corpus fixture.

## Existing recursive authorities

This declaration-body layer reuses previously landed correspondence surfaces. #902 remains the recursive command-closure authority for command occurrences reached through implementation blocks, and #903 remains the deep static-argument closure authority for nested references reached through provider types, propositions, generics, and requirements.

## Evidence boundary

After #904, #906, #907, and this slice, nine of fifteen declaration families have direct body correspondence: record, data, type alias, claim, provider contract, provider implementation, opaque provider implementation, capability, and boundary.

The remaining six are callable contract, function, protocol, component, architecture, and program. `PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted to Implementation Refined.
