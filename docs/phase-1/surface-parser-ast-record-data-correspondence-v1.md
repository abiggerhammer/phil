# Phase 1 surface parser AST record/data correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #903 by beginning the remaining declaration-body layer.

## Closed in this slice

A reusable declaration-common correspondence layer now covers:

- structural modes;
- ordered generic parameters and all nine generic-kind alternatives;
- all thirteen generic-requirement alternatives, with proposition/type/effect payloads delegated to their already-landed correspondence layers; and
- field names plus recursive type payload structure.

On top of that shared layer, record and data declarations now preserve:

- exact declaration name;
- ordered generic parameters;
- omitted versus explicit structural mode;
- ordered generic requirements;
- ordered record fields;
- ordered data variants;
- omitted versus present variant payload;
- record-shaped variant payloads, including empty and trailing-comma field lists; and
- tuple-shaped variant payloads, including empty and nonempty type lists.

The dedicated gate compares complete source through both the extracted certified recognizer and the production parser, includes direct controls for minimal/rich/Unicode forms and mixed record/data source order, and runs over the full accepted Grammar-v1 corpus.

## Composition with earlier closure work

Nested type/proposition/effect payloads reuse the structural projections already landed in #887, #891, and #893. Recursive command occurrences remain covered by #902, and deep static-argument payloads by #903. This slice does not weaken those boundaries or replace them with declaration-local copies.

## Evidence boundary

This closes the declaration shells and ordered payload placement for the `record_decl` and `data_decl` families. The remaining declaration families are `type_alias_decl`, `claim_decl`, `callable_contract_decl`, `function_decl`, `provider_contract_decl`, `provider_implementation_decl`, `opaque_provider_implementation_decl`, `protocol_decl`, `capability_decl`, `boundary_decl`, `architecture_decl`, `component_decl`, and `program_decl`.

`PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**. `PHIL-ASSURE-IMPL-CORR-001` is not promoted until the production AST is mechanically connected to the certified semantics at the required assurance boundary.
