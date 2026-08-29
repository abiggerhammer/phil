# Architecture revision-construction implementation refinement v1

## Status

Production-binding closeout for the revision-construction half of `PHIL-ARCH-ID-IMPL-001`.

## Purpose

`PHIL-ARCH-ID-001` is Certified and the exact rich-identity equality decisions are already production-bound through `ArchitectureIdentityKernel.hs`. The generic assurance validity-scope dependency is now separately production-bound by `PHIL-ASSURE-VALIDITY-IMPL-001`. This closeout binds the remaining concrete architecture revision-construction seam without pretending that Rocq proves Haskell `Text`, `Data.Map`, or the concrete `canonicalSemanticForm` encoder.

## Extracted construction plans

`proof/Phil/Core/ArchitectureRevisionConstructionImplementation.v` extracts typed, polymorphic construction plans for the four architecture identity encodings owned by the Certified ARCH-ID dependency algebra:

1. `InterfaceRevision`: the exact checked interface semantics under the interface-revision namespace;
2. `DefinitionRevision`: the exact interface revision plus exact checked definition semantics under the definition-revision namespace;
3. scoped `InstanceKey`: the exact parent occurrence lineage plus exact stable child slot under the scoped-instance namespace; and
4. `InstanceRevision`: the exact occurrence key, optional parent occurrence, declaration key, interface revision, definition revision, and exact static bindings under the instance-revision namespace.

The plan fields remain polymorphic. Rocq therefore owns the dependency structure without serializing Phil's concrete representation types.

## Production binding

The exact extracted `generated/ArchitectureRevisionConstructionKernel.hs` is checked in byte-for-byte. `Phil.Core.Static` now routes the four Certified construction seams through that kernel:

- `deriveDeclarationIdentity` obtains interface semantics from `planInterfaceRevision`, then obtains the exact interface revision and definition semantics from `planDefinitionRevision` before applying the existing native canonical encoding;
- `deriveArchitectureInstanceIdentity` obtains the occurrence key, parent, declaration key, interface revision, definition revision, and static bindings from `planInstanceRevision`, and constructs both the returned `InstanceKey` and `InstanceRevision` from those plan fields;
- `scopedInstanceKey` obtains the parent and stable slot from `planScopedInstanceKey` before applying the existing scoped-instance encoding; and
- every extracted namespace is matched explicitly. An impossible namespace/shape disagreement terminates fail-closed rather than falling back to a handwritten construction.

Production therefore no longer hand-authors which semantic coordinates constitute these architecture revisions. The extracted plans own that structure; native code only realizes the resulting coordinates into the already-established canonical representation.

## Concrete representation boundary

The following remain explicit primitive representation/runtime foundations rather than claims of the Rocq theorem:

- the finite native mapping from extracted revision namespace to the exact `phil.*.canonical.v1:` prefix;
- the finite native mapping from extracted plan coordinates to the existing canonical record field names;
- `SemanticForm` representation and native equality/ordering;
- `Data.Map.Strict` canonicalization used to materialize semantic records;
- `canonicalSemanticForm`'s concrete `Text` encoding; and
- collision-freedom/injectivity assumptions of that concrete canonical encoding.

These bridges are finite and fail closed when an extracted namespace/shape cannot be represented.

Rocq's Haskell extractor also emits an unused qualified `Prelude` import in this purely polymorphic kernel. To keep the raw extraction byte-identical while preserving strict warnings for handwritten production code, the exact generated source lives under `generated/`, outside the handwritten `src/` search root. Cabal builds it as a private internal library whose only warning exception is `-Wno-unused-imports`; the main `phil-core` library retains the normal strict warning set and depends on that component. This also prevents strict ad-hoc `-isrc` proof and conformance jobs from rediscovering and recompiling the raw generated source outside its component policy.

## Deliberate non-scope

Graph instantiation remains separate. `deriveGraphInstanceIdentity` still owns its graph-specific outer revision over the already-bound base `ArchitectureInstanceIdentity` plus requirement/child/reference semantic bindings. Requirement validation, source-to-checked-semantic elaboration, architecture realization identity, and Systems/StageContract correspondence are likewise not pulled into this slice.

## Validation

The dedicated workflow must:

- recompile the Certified `ArchitectureIdentity.v` model;
- compile the revision-construction correspondence proof;
- fresh-extract `ArchitectureRevisionConstructionKernel.hs` and require byte-for-byte identity with `generated/ArchitectureRevisionConstructionKernel.hs`;
- typecheck the raw extracted kernel under `-Wall -Werror`, suppressing only its generator-owned unused Prelude import;
- validate the Cabal package description and build the generated internal library plus handwritten `phil-core` under warnings-as-errors;
- typecheck the unchanged ARCH-002, ARCH-003, ARCH-004, and ARCH-007 corpora against the built `phil-core` package under `-Wall -Werror`;
- rerun those four unchanged corpora through production; and
- record exact kernel, production module, package-description, and corpus SHA-256 identities in a dedicated production-binding artifact.

An all-green exact head closes the remaining construction boundary for `PHIL-ARCH-ID-IMPL-001`; together with the already-closed generic validity-scope dependency, the row can then become `Discharged / Implementation Refined`.
