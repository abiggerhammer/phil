# Phase 1 generic structural implementation refinement v1

Status: production-binding closeout for `PHIL-GEN-STRUCT-IMPL-001`.

## Scope

This tranche completes the mechanical production-correspondence upgrade for the already Certified `PHIL-GEN-STRUCT-001` / GEN-001–003 structural-polymorphism semantics.

The certified Rocq model is already executable. It represents one already-resolved abstract value parameter with:

- `TransferGenericValue`, which induces no structural permission;
- `DiscardGenericValue`, which induces weakening;
- `DuplicateGenericValue`, which induces contraction;
- a canonical two-bit structural requirement record; and
- exact mode satisfaction for unrestricted, affine, and linear actuals.

The implementation-refinement layer does not define a second structural semantics. It adds an exact diagnostic decision whose accepted result is proved equivalent to the certified `modeSatisfiesRequirements` predicate, then extracts the certified inference and decision functions to Haskell.

## Production binding

`src/GenericStructuralKernel.hs` is the exact Haskell output of Rocq extraction. CI regenerates it from `GenericStructuralImplementationExtraction.v` and rejects any byte difference before the production correspondence job may run.

`Phil.Core.Generic` retains only the concrete representation work that cannot live in the normalized one-parameter proof model:

1. exact `GenericValueParameterKey` identity;
2. duplicate parameter rejection;
3. rejection of uses naming unknown parameters; and
4. grouping concrete use events by exact parameter identity.

For each known parameter, the grouped concrete use events are projected to the extracted `GenericStructuralUse` constructors and the extracted `inferGenericStructuralRequirements` function owns the resulting weakening/contraction requirements.

The Haskell `Set StructuralPermission` representation is converted to and from the extracted two-bit `MkRequirements` form with exact round-trip guards. A bridge mismatch produces `GenericStructuralKernelBridgeMismatch`; bridge code can therefore reject but cannot convert a kernel rejection into success.

Concrete structural-mode checks route through extracted `decideGenericStructuralActual`. Its three results reconstruct exactly the existing public behavior:

- `GenericStructuralActualAccepted` -> success;
- `GenericStructuralActualMissingWeakening` -> `MissingStructuralPermission ... WeakeningPermission ...`;
- `GenericStructuralActualMissingContraction` -> `MissingStructuralPermission ... ContractionPermission ...`.

The certified decision checks weakening before contraction, matching the existing `StructuralPermission` constructor order and prior `Set.toAscList` diagnostic behavior.

`modeAllowsStructuralPermission` is also delegated directly to the extracted kernel. Generic interface checking and structural requirement dispositions therefore transitively exercise the bound structural kernel while their GEN-004+ semantics remain separately certified obligations.

## Verification

The dedicated workflow:

- recompiles the Certified GEN-001–003 model and implementation-refinement theorem;
- freshly extracts `GenericStructuralKernel.hs` under Rocq 9.2.0;
- requires fresh extraction to match `src/GenericStructuralKernel.hs` byte-for-byte;
- typechecks the checked-in kernel and `Phil.Core.Generic` with `-Wall -Werror`;
- reruns the complete GEN-001–003 structural corpus through production; and
- reruns GEN-004–006 requirements tests as a regression because they consume structural inference.

## Residual boundary

Concrete `Text`, `Map`, `Set`, derived Haskell equality/ordering, GHC/runtime behavior, and the Rocq extraction toolchain remain primitive representation/runtime foundations. The canonical runtime round-trip guards make disagreement fail closed.

This refinement does not mechanically connect GEN-004+ published requirement stabilization, generic provider/proposition disposition, application identity, final generic syntax, Systems lowering, or target code generation. Those remain separate implementation-refinement slices.

A green exact-head closeout upgrades `PHIL-GEN-STRUCT-IMPL-001` to `Discharged / Implementation Refined` and records stronger production-correspondence evidence alongside the still-valid `PHIL-GEN-STRUCT-001` Certified semantic row.
