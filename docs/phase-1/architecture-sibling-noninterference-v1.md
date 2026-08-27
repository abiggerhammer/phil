# Phase 1 architecture sibling noninterference v1

Status: implementation conformance slice for `ARCH-007`.

## Property

Changing one architecture child may revise the containing architecture definition without recursively rekeying an unrelated sibling declaration or occurrence. Evidence reuse is governed by each evidence item's declared validity dependencies rather than by blanket invalidation from the containing architecture revision.

This combines two existing Phase 1 rules:

- declaration and occurrence identities are derived from their own stable lineage plus checked semantic inputs, not from the complete revision of a containing declaration; and
- interface-dependent evidence carries a `ValidityScope` dimension keyed by the stable `DeclarationKey` and valued by the exact `InterfaceRevision`.

Therefore a child edit has local consequences:

1. the edited child's identity-bearing semantics may revise its `InterfaceRevision` and `DefinitionRevision`;
2. the containing architecture's `DefinitionRevision` may revise because its composition changed;
3. an unrelated sibling's declaration and instance revisions remain unchanged; and
4. evidence scoped to the edited child's old interface becomes stale, while evidence scoped only to the unaffected sibling remains reusable.

## Pressure case

The dedicated fixture models a small Steve architecture with sibling `store` and `metrics` declarations.

The `metrics` public contract is revised to add a `miss` event. The parent definition records the exact child definition revisions, so the edit revises the parent `DefinitionRevision`. The `store` declaration and `steve.store` occurrence are reconstructed unchanged.

The post-edit assurance context carries current validity dimensions for both siblings. Under that one context:

- old `store` interface evidence still verifies;
- old `metrics` interface evidence rejects with `EvidenceValidityScopeMismatch`; and
- fresh evidence scoped to the revised `metrics` interface verifies.

This is intentionally selective. ARCH-007 does not claim that all evidence survives a sibling edit, only that evidence is invalidated according to its declared semantic dependencies rather than by accidental containment.

## Dedicated corpus

`test/Phase1ArchitectureSiblingNoninterferenceMain.hs` checks seven cases:

1. the edited child preserves its stable lineage key but revises its own interface and definition revisions;
2. the parent preserves its interface while revising its definition;
3. the unaffected sibling declaration identity remains exact;
4. the unaffected sibling occurrence remains exact across the parent revision;
5. sibling-scoped evidence remains valid after the peer edit;
6. evidence scoped to the edited child's old interface rejects; and
7. fresh evidence for the edited child verifies.

The corpus is wired into ordinary CI as `Phase 1 architecture sibling noninterference conformance`.
