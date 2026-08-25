# Phase 1 generic structural requirements v1

This tranche begins logic-ledger obligation `PHIL-GEN-STRUCT-001` and conformance cases `GEN-001`–`GEN-003`.

The bounded semantic rule is inherited directly from Phil's existing structural modes:

- transferring one abstract value occurrence requires neither weakening nor contraction;
- discarding an abstract value induces `WeakeningPermission`;
- duplicating an abstract value induces `ContractionPermission`;
- `Unrestricted` actuals satisfy both permissions;
- `Affine` actuals satisfy weakening only;
- `Linear` actuals satisfy neither.

`Phil.Core.Generic` operates on checked semantic use events rather than surface syntax. It computes a canonical minimum permission set per stable abstract-value parameter and checks an exact concrete `Mode` against that set. Generic structural requirements are therefore consequences of ADR-002, not a parallel Copy/Drop trait system.

The executable corpus checks structure-polymorphic identity over a linear actual, inferred weakening and contraction, combined requirements, canonical ordering, independent parameter requirements, and fail-closed unknown/duplicate parameter identities.

This slice does not yet claim the Rocq proof for `PHIL-GEN-STRUCT-001`, final generic syntax, generic type variables in Core, declared/stabilized public requirement sets (`PHIL-GEN-REQ-001`), provider/proposition requirements, generic instantiation identity, callable capture modes, or any lowering/monomorphization strategy.
