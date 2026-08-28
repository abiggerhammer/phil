# Phase 1 architecture identity proof v1

This note defines the bounded Rocq proof authority for `PHIL-ARCH-ID-001`, covering the already-implemented ARCH-002, ARCH-003, ARCH-004, and ARCH-007 identity semantics.

## Certified semantic surface

`proof/Phil/Core/ArchitectureIdentity.v` models declaration and occurrence identity independently of any concrete serialization or digest representation.

It proves:

- **presentation noninterference (ARCH-002):** changing a human display name or module location while preserving stable declaration lineage and checked semantics preserves the exact `DeclarationIdentity` and downstream architecture-instance identity;
- **public interface revision (ARCH-003):** changing checked public interface semantics preserves `DeclarationKey`, changes `InterfaceRevision`, necessarily changes `DefinitionRevision`, and changes the interface-validity scope value while keeping its dimension keyed by stable declaration lineage;
- **definition replacement (ARCH-004):** changing checked definition/body/composition semantics under one unchanged public interface preserves `InterfaceRevision` and interface-scoped evidence validity while changing `DefinitionRevision`; and
- **sibling noninterference (ARCH-007):** a child occurrence is keyed from stable parent occurrence lineage plus its stable slot, and its revision is derived from its own declaration identity and bindings rather than the containing declaration's complete definition revision. A peer edit may therefore revise the parent definition without rekeying an unaffected child or changing that child's interface-validity scope.

## Deliberate abstraction

The Rocq theorem uses abstract semantic values and structural revision records. It does **not** claim that Rocq proves the current Text encoding in `Phil.Core.Static` or SHA/canonical serialization correctness.

Production currently represents revision identities through versioned canonical `SemanticForm` serialization. The following remain explicit correspondence/representation foundations:

- concrete Text-backed `DeclarationKey`, revision, and occurrence-key representation;
- `Map`/`Set` canonicalization and ordering;
- canonical `SemanticForm` serialization;
- any later digest collision-resistance assumption;
- source-to-checked-semantic elaboration; and
- the truth of the competent checker that decides whether a changed implementation still refines an unchanged public interface.

The proof establishes the semantic dependency structure that any such representation must preserve.

## Executable correspondence pressure

The dedicated workflow reruns the existing implementation corpora unchanged:

- `Phase1ArchitectureRenameIdentityMain.hs` for ARCH-002;
- `Phase1ArchitectureInterfaceValidityMain.hs` for ARCH-003;
- `Phase1ArchitectureDefinitionReplacementMain.hs` for ARCH-004; and
- `Phase1ArchitectureSiblingNoninterferenceMain.hs` for ARCH-007.

Those tests remain implementation evidence; they are not substituted for the Rocq theorem.

On green, `PHIL-ARCH-ID-001` may be upgraded from `Active / Tested` to `Discharged / Certified`. Mechanical production correspondence beyond this formal-model certification remains a later `Implementation Refined` tranche under `PHIL-ASSURE-IMPL-CORR-001`.
