# Architecture revision-construction implementation refinement v1

## Status

Staging / Mechanized target for the revision-construction half of `PHIL-ARCH-ID-IMPL-001`.

## Purpose

`PHIL-ARCH-ID-001` is Certified and the exact rich-identity equality decisions are already production-bound through `ArchitectureIdentityKernel.hs`. Two boundaries still prevent `PHIL-ARCH-ID-IMPL-001` from reaching `Implementation Refined`: generic assurance validity-scope composition and concrete architecture revision construction.

The validity-scope dependency is being refined independently through `PHIL-ASSURE-VALIDITY-IMPL-001`. This tranche isolates the other half without pretending that Rocq proves Haskell `Text`, `Data.Map`, or the concrete `canonicalSemanticForm` encoder.

## Extracted construction plans

`proof/Phil/Core/ArchitectureRevisionConstructionImplementation.v` extracts typed, polymorphic construction plans for the four architecture identity encodings owned by the Certified ARCH-ID dependency algebra:

1. `InterfaceRevision`: the exact checked interface semantics under the interface-revision namespace;
2. `DefinitionRevision`: the exact interface revision plus exact checked definition semantics under the definition-revision namespace;
3. scoped `InstanceKey`: the exact parent occurrence lineage plus exact stable child slot under the scoped-instance namespace; and
4. `InstanceRevision`: the exact occurrence key, optional parent occurrence, declaration key, interface revision, definition revision, and exact static bindings under the instance-revision namespace.

The plan fields are polymorphic. Rocq therefore owns the dependency structure without serializing Phil's concrete representation types. The production-binding tranche can instantiate those fields directly with native `SemanticForm`, `InterfaceRevision`, `DefinitionRevision`, `InstanceKey`, `OccurrenceSlotKey`, and binding-map values.

## Correspondence to the Certified model

The proof composes directly with `ArchitectureIdentity.v` and establishes that every extracted plan coordinate is exactly the coordinate used by the Certified derivation:

- interface-plan semantics equal the Certified `identityInterfaceRevision` input;
- definition-plan interface/body equal the two fields of Certified `DefinitionRevision`;
- scoped-key plan parent/slot are exactly the arguments of Certified `ScopedInstanceKey`; and
- instance-plan fields equal every field of Certified `InstanceRevision`.

Negative controls show that a changed definition body, scoped parent, scoped slot, static binding, or instance interface cannot leave the corresponding construction plan unchanged.

## Concrete representation boundary retained

This staging tranche deliberately leaves production unchanged. The later binding will translate the extracted plans into the existing canonical representation. The following remain explicit primitive representation foundations rather than claims of the Rocq theorem:

- the finite native mapping from extracted revision namespace to the exact `phil.*.canonical.v1:` prefix;
- the finite native mapping from extracted plan coordinates to the existing canonical record field names;
- `SemanticForm` representation and native equality/ordering;
- `Data.Map.Strict` canonicalization used to materialize semantic records;
- `canonicalSemanticForm`'s concrete `Text` encoding; and
- collision-freedom/injectivity assumptions of that concrete canonical encoding.

Those bridges must be small, total, directly tested, and fail closed where an extracted namespace/shape cannot be represented. The important refinement is that production will no longer hand-author which semantic coordinates constitute each architecture revision: that structure comes from the extracted kernel.

Graph instantiation, requirement validation, source-to-checked-semantic elaboration, architecture realization identity, and Systems/StageContract correspondence remain separate obligations and are not pulled into this slice.

## Validation

The dedicated workflow must:

- recompile the Certified `ArchitectureIdentity.v` model;
- compile the revision-construction correspondence proof;
- fresh-extract `ArchitectureRevisionConstructionKernel.hs`;
- typecheck the extracted polymorphic kernel under `-Wall -Werror`;
- typecheck the unchanged production `Phil.Core.Static` path; and
- rerun the unchanged ARCH-002, ARCH-003, ARCH-004, and ARCH-007 corpora.

A green staging run adds mechanized evidence for the exact revision dependency structure only. It does not yet bind production and therefore does not by itself close `PHIL-ARCH-ID-IMPL-001`.
