# Architecture instantiation decision implementation refinement v1

## Status

Staging refinement for the decision surface of Certified `PHIL-ARCH-INST-001`.

## Scope

`proof/Phil/Core/ArchitectureInstantiation.v` already owns four executable, representation-neutral decisions used by the architecture-instantiation semantics:

- duplicate versus fresh child occurrence slot;
- explicit requirement disposition, including missing binding target and interface mismatch;
- the same decision at the root, preserving the no-magical-initial-binding rule; and
- explicit-reference target existence.

This staging slice extracts those Certified decisions without changing production behavior. Concrete Haskell graph construction remains unchanged until a production-binding closeout.

## Native reflection boundary

The eventual production bridge will continue to compute concrete finite facts natively:

- child-slot freshness from exact finite-map membership;
- whether a requirement has an explicit disposition and whether that disposition is `RequirementBoundTo`;
- exact target existence from checked graph lookup;
- exact expected/actual `InterfaceRevision` equality when an interface is required; and
- explicit-reference target existence from checked graph lookup.

The extracted kernel owns the final semantic decision over those reflected facts. A closeout bridge may fail closed on disagreement, but may not convert kernel rejection into success.

Duplicate requirement keys, duplicate reference keys, map normalization/traversal, concrete diagnostics, and source occurrence-site elaboration remain native representation/correspondence boundaries unless separately mechanized.

## Deliberate non-scope

The graph-specific outer `InstanceRevision` constructed by `deriveGraphInstanceIdentity` includes requirement, child, and reference semantic bindings. The current Certified `ArchitectureInstantiation.v` model does not characterize that richer concrete serialization. This staging slice therefore does **not** claim a proof for it. That boundary remains open for a Certified semantic refinement or a separate obligation rather than being strengthened here implicitly.

The already-refined ARCH-ID layer continues to own scoped `InstanceKey` construction and base architecture-instance identity construction.

## Validation

The dedicated workflow must:

- recompile `ArchitectureIdentity.v` and Certified `ArchitectureInstantiation.v`;
- compile `ArchitectureInstantiationImplementation.v` outcome characterizations;
- fresh-extract `ArchitectureInstantiationKernel.hs`;
- typecheck and directly execute the extracted decision kernel controls;
- strict-typecheck unchanged `Phil.Core.Static` and the unchanged ARCH-005/006/008/009 corpus;
- rerun all 11 existing architecture-instantiation cases unchanged; and
- record exact proof, extracted-kernel, production-module, and corpus identities in CI artifacts.

An all-green exact head establishes a staged `Mechanized` implementation boundary. Production behavior remains unchanged until the follow-up binding PR.
