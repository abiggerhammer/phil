# Phase 1 architecture rename identity conformance v1

Status: bounded executable conformance slice for `ARCH-002`.

## Governing rule

A declaration's human presentation is not its semantic identity.

If a checked declaration keeps the same stable `DeclarationKey`, public interface semantics, and checked definition semantics, then changing its display name, source module path, or both must preserve the same `DeclarationIdentity`:

- `DeclarationKey` is unchanged;
- `InterfaceRevision` is unchanged; and
- `DefinitionRevision` is unchanged.

Because architecture occurrences bind the checked declaration identity rather than its presentation, the same presentation-only edit must also preserve the downstream `ArchitectureInstanceRevision` when the occurrence key, parent lineage, and static bindings are unchanged.

This is the executable `ARCH-002` boundary from ADR-019. Source positions, filenames, mutable names, and module organization may participate in diagnostics and lookup, but they are not generative semantic identity.

## Existing semantic implementation

`Phil.Core.Static.DeclarationDescriptor` stores `DeclarationPresentation` separately from the stable key and checked semantic forms. `deriveDeclarationIdentity` deliberately derives revisions only from:

- `declarationKey` for stable lineage;
- `declarationInterfaceSemantics` for `InterfaceRevision`; and
- the exact interface revision plus `declarationDefinitionSemantics` for `DefinitionRevision`.

`declarationPresentation` is not an identity input.

The original architecture-identity bootstrap test already exercised a combined rename/module-move case. This slice promotes that property into a dedicated Phase 1 conformance gate so the matrix no longer depends on a buried monolithic test.

## Dedicated corpus

`test/Phase1ArchitectureRenameIdentityMain.hs` checks:

1. human display-name rename preserves exact declaration identity;
2. module-path move preserves exact declaration identity;
3. rename plus module move preserves exact declaration identity;
4. presentation-only change preserves the downstream architecture instance revision; and
5. an identity-bearing definition semantic change still revises `DefinitionRevision`, proving the invariance check is not vacuous.

The dedicated CI step is `Phase 1 architecture rename identity conformance`.

## Boundary of this slice

This slice closes only `ARCH-002`.

The adjacent architecture rows remain distinct obligations:

- `ARCH-003` additionally requires public-contract revision and validity-dependent evidence invalidation;
- `ARCH-004` covers definition replacement under a stable public interface;
- `ARCH-007` covers unaffected sibling lineage together with validity-dependent evidence reuse; and
- `ARCH-010` covers realization replacement under stable abstract architecture identity.

The old bootstrap cases are useful implementation evidence for those rows, but they do not by themselves establish every conformance clause now recorded in the Phase 1 matrix.
