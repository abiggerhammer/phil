# Phase 1 surface parser AST capability/boundary correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #906 by closing the `capability_decl` and `boundary_decl` declaration bodies.

## Closed in this slice

Capability correspondence preserves:

- declaration name;
- ordered generic parameters;
- mandatory structural mode;
- ordered generic requirements;
- ordered `permits`, `requires`, and named `law` items;
- exact static-reference payloads for `permits`; and
- exact proposition payloads for `requires` and laws.

Boundary correspondence preserves:

- declaration name;
- ordered generic parameters and requirements;
- boundary type;
- ordered `receive using`, `send using`, `correspondence`, `canonical`, `failure`, and named `law` items;
- exact static-reference payloads for receive/send transports;
- exact proposition payloads for correspondence/laws; and
- exact failure type payloads.

The direct harness covers all nine item alternatives across the two declaration families, minimal and rich forms, Unicode identifiers, mixed sources, and an adversarial boundary-failure type mismatch. The permanent gate also compares every accepted parser-corpus fixture through the certified recognizer and production parser.

#902 remains the recursive command-closure authority and #903 remains the deep static-argument closure authority for nested payloads reached through these declarations.

## Evidence boundary

With #904, #906, and this slice, six of the fifteen declaration families have direct declaration-body correspondence: record, data, type alias, claim, capability, and boundary. Nine declaration families remain open: callable contract, function, provider contract, provider implementation, opaque provider implementation, protocol, component, architecture, and program.

`PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted to Implementation Refined.
