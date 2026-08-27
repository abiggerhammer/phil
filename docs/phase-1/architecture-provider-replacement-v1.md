# Phase 1 architecture provider replacement conformance

This note records the executable `ARCH-010` boundary between target-abstract architecture identity and build-scoped provider realization identity.

The governing rule is:

> Replacing one independently qualified implementation for the same abstract provider binding preserves `ArchitectureInstance` and changes `ArchitectureRealization` plus implementation-specific qualification/evidence lineage.

This is a build-time realization substitution. It is not live provider migration.

## Semantic topology versus execution topology

The abstract architecture records the provider occurrence and required provider interface, not the selected concrete implementation. Consequently the selected implementation is not an input to `ArchitectureInstanceRevision`.

The selected implementation and its exact qualification material are realization facts. The ARCH-010 pressure fixture therefore derives one exact Steve store `ArchitectureInstanceIdentity`, then derives two `ArchitectureRealizationIdentity` values over that same instance:

- realization I1 selects a filesystem-style BlobProvider implementation;
- realization I2 selects an object-store-style BlobProvider implementation.

Both implementations derive the same provider `InterfaceRevision` and distinct `DefinitionRevision` values.

## Qualification lineage is realization content

Each realization records the selected implementation definition together with exact provider qualification claim, evidence, admission, and artifact identities. Replacing I1 with I2 therefore changes all of:

- selected implementation `DefinitionRevision`;
- provider qualification claim revision;
- provider qualification evidence revision;
- provider qualification admission revision;
- selected implementation artifact; and
- `RealizationRevision`.

The provider-replacement checker must agree with the architecture-derived identities. It may not accept a different `InstanceRevision`, an unchanged realization revision, inherited implementation subject, or stale predecessor evidence.

The two independent qualification bundles deliberately share one provider-contract validity dependency. PROV-015 treats that shared dependency as evidence reuse rather than ambient common context, so ARCH-010 supplies an explicit cross-claim reuse justification naming both exact qualification claim revisions and a nonempty validity-scope revision. The checker must report that reuse explicitly. Implementation-specific proof references remain distinct and are not inherited across the replacement.

## Dedicated corpus

`test/Phase1ArchitectureProviderReplacementMain.hs` checks nine cases:

1. both independently described implementations expose the same abstract provider interface and distinct definitions;
2. provider replacement preserves the exact derived `ArchitectureInstanceRevision`;
3. the selected implementation change revises the derived `ArchitectureRealizationRevision`;
4. the provider-replacement checker accepts the pair and records the explicitly justified shared provider-contract validity dependency;
5. the checker reports the exact architecture-derived instance and realization revisions;
6. claim, evidence, and admission lineage all change;
7. rebuilding the same exact selected realization deterministically reproduces its revision;
8. predecessor evidence cannot be rebound to the replacement claim; and
9. changing the abstract architecture occurrence is rejected as a topology change rather than treated as provider replacement.

## Scope

This closes `ARCH-010` only. It composes existing architecture identity and PROV-015 provider-replacement semantics; it does not add a second provider qualification mechanism or claim that Systems artifacts are byte-identical across replacements. Systems and StageContract may change and must be regenerated/revalidated where required.
