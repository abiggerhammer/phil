# Architecture Identity Implementation Refinement v1

## Status

Active / Mechanized target for `PHIL-ARCH-ID-IMPL-001`.

## Purpose

`PHIL-ARCH-ID-001` is Certified, but its production implementation still contains representation boundaries between the normalized Rocq model and concrete Haskell identity values. The implementation-refinement work therefore proceeds in bounded executable seams rather than pretending the proof certifies concrete `Text` serialization.

PR #341 established the first executable kernel without changing production behavior. This tranche binds the exact harvested kernel into production identity equality while retaining concrete revision construction as a separately named correspondence obligation.

## Executable kernel

`proof/Phil/Core/ArchitectureIdentityImplementation.v` defines three representation-neutral decisions over primitive equality facts supplied by the production representation layer:

1. exact `DeclarationIdentity` equality from stable declaration-key equality, exact interface-revision equality, and exact definition-revision equality;
2. exact interface-validity-scope equality from stable declaration-key equality and exact interface-revision equality, deliberately excluding definition revision; and
3. exact `ArchitectureInstanceIdentity` equality from exact `InstanceKey` equality and exact `InstanceRevision` equality.

The correspondence theorems prove each Boolean decision sound and complete for the corresponding Certified relation when the supplied native equality facts faithfully reflect the concrete components. Separate theorems pin the intended negative controls: definition-revision difference rejects declaration identity equality but does not enter interface-validity scope; interface-revision difference invalidates the interface scope; and instance-revision difference rejects exact architecture-instance identity equality.

`ArchitectureIdentityImplementationExtraction.v` extracts only these fact records and decisions to Haskell. No `Text`, `SemanticForm`, `Map`, key, revision, or rich Phil identity is serialized through Rocq.

## Production binding

The exact kernel harvested from #341 is checked in as `src/ArchitectureIdentityKernel.hs`. The dedicated workflow fresh-extracts it on every run and requires byte-for-byte equality before production validation.

`Phil.Core.Static` now routes the `Eq` instances for the two rich identity records through that extracted kernel:

- `DeclarationIdentity` supplies native equality facts for `DeclarationKey`, `InterfaceRevision`, and `DefinitionRevision`; the extracted decision is authoritative for equality;
- `ArchitectureInstanceIdentity` supplies native equality facts for `InstanceKey` and `InstanceRevision`; the extracted decision is authoritative for equality.

`Ord` remains structurally derived from the same concrete component order. A direct binding corpus checks representative `Eq`/`Ord` consistency and independently exercises every equality coordinate.

The interface-validity-scope decision remains Mechanized but is not rebound here. Concrete architecture validity dimensions are consumed by the generic `Phil.Assurance.Verify` validity-scope machinery, which is itself governed by the separate Certified `PHIL-ASSURE-VALIDITY-001` theorem family. Composing the architecture-specific equality kernel into that already-Certified generic verifier is a separate bounded refinement step; this slice does not replace or bypass the generic validity-scope authority.

## Representation boundary still open

This tranche still does **not** claim mechanical correspondence for:

- `canonicalSemanticForm` or its concrete `Text` encoding;
- construction of `InterfaceRevision`, `DefinitionRevision`, `InstanceKey`, or `InstanceRevision` bytes;
- `Map`/`Set` canonicalization or ordinary native primitive equality/ordering;
- source-to-checked-semantic elaboration;
- architecture graph construction or requirement validation; or
- realization identity / Systems / StageContract correspondence.

Those remain explicit representation/correspondence boundaries. In particular, production-binding equality through the extracted kernel is necessary but not sufficient to upgrade `PHIL-ARCH-ID-IMPL-001` to `Discharged / Implementation Refined` under `PHIL-ASSURE-IMPL-CORR-001`.

## Validation

The dedicated workflow must:

- recompile the Certified `ArchitectureIdentity.v` model;
- compile the implementation correspondence proof;
- fresh-extract `ArchitectureIdentityKernel.hs`;
- require byte-for-byte equality with the checked-in production kernel;
- typecheck the generated kernel and bound production paths under `-Wall -Werror`;
- rerun the unchanged ARCH-002, ARCH-003, ARCH-004, and ARCH-007 corpora;
- run a direct production-binding corpus over every extracted equality coordinate and representative `Eq`/`Ord` consistency; and
- record exact production correspondence hashes as a separate CI artifact.

A green run extends `Active / Mechanized` evidence from staging into actual production equality binding. Final `Implementation Refined` closeout still requires the remaining architecture validity-scope composition and concrete revision-construction correspondence boundaries to be mechanically resolved or explicitly narrowed by a later proof/refinement decision.
