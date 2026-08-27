# Phase 1 architecture interface validity v1

Status: bounded executable conformance slice for `ARCH-003` and `PHIL-ARCH-ID-001`.

## Governing rule

A stable declaration lineage is not a promise that all evidence about every revision of that declaration remains reusable.

The ARCH-003 rule is:

> Changing an identity-bearing public provider/callable/generic/protocol/architecture requirement changes `InterfaceRevision`, and evidence whose declared validity depends on the old public interface is invalid under the new interface unless fresh evidence is supplied for that exact revision.

A definition/body/composition rewrite that still refines the same public interface is different: it changes `DefinitionRevision` but does not invalidate evidence whose validity scope names only the unchanged `InterfaceRevision`.

## Existing assurance mechanism

Phil already has the needed fail-closed mechanism:

- every `EvidenceEntry` has a `ValidityScope`;
- each manifest carries an explicit validity context;
- `verifyManifest` requires every evidence validity dimension to equal the active context value;
- stale scoped evidence rejects with `EvidenceValidityScopeMismatch`.

ARCH-003 therefore does not introduce a second evidence or invalidation system.

## Architecture/interface bridge

`Phil.Assurance.ArchitectureIdentity` defines one versioned validity dimension per stable declaration lineage:

```text
phil.arch.interface-revision.v1:<DeclarationKey>
```

The dimension value is the exact `InterfaceRevision`.

This choice is deliberate:

- the dimension key follows stable declaration lineage;
- human display names and module paths do not affect it;
- a public-contract change changes the dimension value;
- a definition-only rewrite under the same public interface leaves it unchanged;
- several declaration interfaces can coexist in one manifest as distinct validity dimensions.

The bridge provides:

- `interfaceValidityDimension`;
- `interfaceValidityContext`; and
- `interfaceValidityScope`.

## Conformance corpus

The dedicated ARCH-003 corpus checks:

1. a public-contract change preserves `DeclarationKey` and revises both `InterfaceRevision` and `DefinitionRevision`;
2. the interface-validity dimension key follows stable declaration lineage while its value changes with `InterfaceRevision`;
3. evidence scoped to the current interface verifies;
4. the same old evidence rejects after a public-interface revision with `EvidenceValidityScopeMismatch`;
5. fresh evidence scoped to the revised interface verifies; and
6. a definition-only replacement changes `DefinitionRevision` while preserving the interface-scoped evidence validity.

The sixth case is a non-overinvalidation control. It supports the ARCH-003 distinction but does not by itself close the broader ARCH-004 row.

## Boundary

This slice does not yet prove the general declaration-identity theorem in Rocq and does not close every evidence-validity consequence of ARCH-004 or ARCH-007.

`PHIL-ARCH-ID-001` therefore remains Active / Tested after this slice lands. ARCH-004, ARCH-007, and the declaration-identity proof remain separately open.
