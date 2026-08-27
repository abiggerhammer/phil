# Phase 1 generic requirements implementation refinement v1

Status: production-binding closeout for `PHIL-GEN-REQ-IMPL-001`.

## Scope

This tranche completes the mechanical production-correspondence upgrade for the already Certified `PHIL-GEN-REQ-001` / GEN-004–006 public generic structural-requirement semantics.

The certified model defines componentwise public-contract coverage and stabilized publication. #275 added the executable three-way decision whose accepted result is proved equivalent both to certified `requirementsCover published induced = true` and to successful explicit publication of that same public contract. This closeout checks in that exact extracted kernel and routes production explicit-publication coverage through it.

The extracted decision preserves the existing structural diagnostic order: missing weakening is reported before missing contraction.

## Production binding

`src/GenericRequirementsKernel.hs` is the exact Haskell extraction produced by the #275 proof tranche. The dedicated refinement workflow regenerates it from Rocq and requires byte-for-byte equality with the checked-in file before correspondence testing proceeds.

`Phil.Core.Generic` retains the concrete outer representation work that is not part of the normalized proof model:

1. exact `GenericValueParameterKey` / `Text` identity;
2. duplicate generic value parameter rejection;
3. duplicate explicit published-requirement rejection;
4. unknown published parameter rejection;
5. omitted explicit published parameters represented by the empty requirement set; and
6. implicit publication as the exact already-inferred induced map.

Those checks establish the parameter domain and normalized published map. For each induced parameter in canonical `Map.toAscList` order, production then converts the published and induced `Set StructuralPermission` values to the extracted weakening/contraction-bit representation. The conversion is guarded by an exact round trip through the concrete Haskell representation; disagreement returns `GenericRequirementsKernelBridgeMismatch` and therefore fails closed.

Once converted, `ensurePublishedCoversInduced` delegates acceptance and the first missing structural permission to extracted `decideGenericRequirementsCoverage`. Handwritten code only reconstructs the existing `PublishedStructuralRequirementTooWeak` diagnostic from the extracted decision constructors; it cannot turn an extracted rejection into acceptance.

The preceding `PHIL-GEN-STRUCT-IMPL-001` binding supplies mechanically refined structural-use inference, so the induced requirement map consumed here is itself produced through the certified structural kernel.

## Correspondence checks

The dedicated workflow requires all of the following on the exact tree:

- the Certified `GenericRequirements.v` model and executable implementation proof compile under Rocq;
- fresh `GenericRequirementsKernel.hs` extraction is byte-identical to `src/GenericRequirementsKernel.hs`;
- the checked-in kernel typechecks with `-Wall -Werror`;
- production `Phil.Core.Generic` and the GEN-004–006 test driver typecheck with `-Wall -Werror`; and
- the complete existing GEN-004–006 correspondence corpus runs through the bound production tree.

This covers exact inferred minimum publication, order independence, intentionally stronger public contracts, stable body evolution within a contract, fail-closed body growth beyond the contract, omitted permissions as empty, unknown published keys, and duplicate published keys.

## Residual trust boundary

After a green closeout, the remaining primitive foundations for this bounded slice are Rocq kernel/extraction-toolchain correctness, GHC/Haskell runtime behavior, `containers` `Map`/`Set` semantics, `Text`, and ordinary derived Haskell equality/ordering. Provider/callable/proposition requirements, generic instantiation and application identity, final syntax, Systems lowering, and target code generation are separate refinement slices.

A green exact-head closeout upgrades `PHIL-GEN-REQ-IMPL-001` to `Discharged / Implementation Refined`.
