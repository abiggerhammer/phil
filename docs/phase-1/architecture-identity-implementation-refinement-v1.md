# Architecture Identity Implementation Refinement v1

## Status

Staging / Mechanized target for `PHIL-ARCH-ID-IMPL-001`.

## Purpose

`PHIL-ARCH-ID-001` is Certified, but its production implementation still relies on reviewed correspondence between the representation-neutral Rocq model and concrete Haskell identity values. This tranche begins the mechanical implementation-refinement migration without changing production behavior.

The first executable seam is identity equality itself. It is deliberately narrower than concrete revision serialization.

## Executable kernel

`proof/Phil/Core/ArchitectureIdentityImplementation.v` defines three representation-neutral decisions over primitive equality facts supplied by the production representation layer:

1. exact `DeclarationIdentity` equality from stable declaration-key equality, exact interface-revision equality, and exact definition-revision equality;
2. exact interface-validity-scope equality from stable declaration-key equality and exact interface-revision equality, deliberately excluding definition revision; and
3. exact `ArchitectureInstanceIdentity` equality from exact `InstanceKey` equality and exact `InstanceRevision` equality.

The correspondence theorems prove each Boolean decision sound and complete for the corresponding Certified relation when the supplied native equality facts faithfully reflect the concrete components. Separate theorems pin the intended negative controls: definition-revision difference rejects declaration identity equality but does not enter interface-validity scope; interface-revision difference invalidates the interface scope; and instance-revision difference rejects exact architecture-instance identity equality.

`ArchitectureIdentityImplementationExtraction.v` extracts only these fact records and decisions to Haskell. No `Text`, `SemanticForm`, `Map`, key, revision, or rich Phil identity is serialized through Rocq.

## Production boundary retained in this staging tranche

Production remains unchanged. In particular, this tranche does **not** yet claim mechanical correspondence for:

- `canonicalSemanticForm` or its concrete `Text` encoding;
- construction of `InterfaceRevision`, `DefinitionRevision`, `InstanceKey`, or `InstanceRevision` bytes;
- `Map`/`Set` canonicalization or ordinary native equality/ordering;
- source-to-checked-semantic elaboration;
- architecture graph construction or requirement validation; or
- realization identity / Systems / StageContract correspondence.

Those remain explicit representation/correspondence boundaries.

A later closeout tranche may check in the exact extracted kernel and route production architecture-identity comparisons through it with fail-closed component bridges. Concrete revision construction remains separately reviewable and must receive whatever additional mechanical bridge is needed before `PHIL-ARCH-ID-IMPL-001` can become `Discharged / Implementation Refined` under `PHIL-ASSURE-IMPL-CORR-001`.

## Validation

The dedicated workflow must:

- recompile the Certified `ArchitectureIdentity.v` model;
- compile the implementation correspondence proof;
- fresh-extract `ArchitectureIdentityKernel.hs`;
- typecheck the generated kernel under `-Wall -Werror`;
- typecheck the unchanged architecture identity production paths; and
- rerun the unchanged ARCH-002, ARCH-003, ARCH-004, and ARCH-007 corpora.

A green staging run earns `Active / Mechanized` evidence for this bounded equality seam only. It does not yet upgrade the architecture identity obligation to `Implementation Refined`.
