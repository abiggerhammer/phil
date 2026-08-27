# Phase 1 generic structural implementation refinement v1

Status: executable proof/extraction tranche for `PHIL-GEN-STRUCT-IMPL-001`.

## Scope

This tranche begins the mechanical production-correspondence upgrade for the already Certified `PHIL-GEN-STRUCT-001` / GEN-001–003 structural-polymorphism semantics.

The certified Rocq model is already executable. It represents one already-resolved abstract value parameter with:

- `TransferGenericValue`, which induces no structural permission;
- `DiscardGenericValue`, which induces weakening;
- `DuplicateGenericValue`, which induces contraction;
- a canonical two-bit structural requirement record; and
- exact mode satisfaction for unrestricted, affine, and linear actuals.

The implementation-refinement layer does not define a second structural semantics. It adds an exact diagnostic decision whose accepted result is proved equivalent to the certified `modeSatisfiesRequirements` predicate, then extracts the certified inference and decision functions to Haskell.

## Production bridge boundary

The later production-binding tranche must connect `Phil.Core.Generic` to the extracted kernel without allowing handwritten code to strengthen acceptance.

The concrete bridge must account for:

1. exact `GenericValueParameterKey` identity;
2. duplicate parameter rejection;
3. rejection of uses naming unknown parameters;
4. canonical grouping of uses by exact parameter identity;
5. exact conversion between the Haskell `Set StructuralPermission` and the certified weakening/contraction bits; and
6. exact preservation of the first missing permission diagnostic (`WeakeningPermission` before `ContractionPermission`, matching the current derived `Ord` / `Set.toAscList` behavior).

Concrete `Text`, `Map`, `Set`, and derived Haskell equality/ordering remain representation foundations. The final bridge must use canonical round-trip checks and may only fail closed.

## Evidence level

A green proof/extraction tranche establishes the executable kernel and earns `Mechanized` for the bounded implementation-refinement obligation. It does **not** by itself upgrade `PHIL-GEN-STRUCT-001` to `Implementation Refined`.

That upgrade requires a subsequent exact production binding with byte-identical fresh extraction and the existing GEN-001–003 corpus running through the extracted decision path.
