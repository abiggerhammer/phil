# Phase 1 generic requirements implementation refinement v1

Status: executable proof/extraction tranche for `PHIL-GEN-REQ-IMPL-001`.

## Scope

This tranche begins the mechanical production-correspondence upgrade for the already Certified `PHIL-GEN-REQ-001` / GEN-004–006 public generic structural-requirement semantics.

The certified model already defines componentwise public-contract coverage and stabilized publication. This tranche therefore does not introduce a second publication semantics. It adds an exact executable coverage diagnostic whose accepted result is proved equivalent to both:

- certified `requirementsCover published induced = true`; and
- certified successful explicit publication of that same `published` contract.

The extracted decision preserves the existing structural diagnostic order: missing weakening is reported before missing contraction.

## Production bridge boundary

The later production-binding tranche must connect `Phil.Core.Generic` to the extracted coverage kernel while preserving the concrete outer representation checks:

1. exact `GenericValueParameterKey` identity;
2. duplicate generic value parameter rejection;
3. duplicate explicit published-requirement rejection;
4. unknown published parameter rejection;
5. implicit publication as the exact already-inferred induced map;
6. canonical per-key `Set StructuralPermission` ↔ weakening/contraction-bit conversion; and
7. exact first-missing-permission diagnostics.

The just-completed `PHIL-GEN-STRUCT-IMPL-001` production binding supplies the mechanically refined structural inference used to construct the induced requirement map. Concrete `Text`, `Map`, `Set`, and derived Haskell equality/ordering remain representation foundations. Bridge disagreement must fail closed.

## Evidence level

A green proof/extraction tranche earns `Mechanized` for the bounded `PHIL-GEN-REQ-IMPL-001` obligation. It does not yet earn `Implementation Refined`.

Final closeout requires checking in the exact generated kernel, requiring byte-identical fresh extraction, and routing production GEN-004–006 explicit-publication coverage acceptance through the extracted decision while retaining the existing duplicate/unknown-key checks as fail-closed representation logic.
