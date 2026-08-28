# Phase 1 architecture realization proof v1

Status: Rocq proof tranche for `PHIL-ARCH-REALIZE-001` and conformance case `ARCH-010`.

## Certified claim

Architecture realization is downstream of the exact abstract architecture occurrence.

The proof establishes a representation-neutral realization revision carrying:

- the exact architecture `InstanceKey`;
- the exact architecture `InstanceRevision`; and
- identity-bearing realization semantics.

From that model:

- rebuilding the same selected realization is deterministic;
- changing realization semantics under the same abstract instance changes realization identity;
- changing the abstract instance key or revision changes realization identity; and
- realization derivation itself does not revise the abstract architecture occurrence.

## Provider replacement composition

ARCH-010 does not define a second provider-replacement checker. The proof composes the already-Certified `PHIL-PROV-REPLACE-001` theorem family.

For a valid provider replacement, the provider theorem already requires:

- exact `InstanceRevision` preservation;
- a different realization revision;
- distinct qualification claim/evidence/admission lineage;
- rejection of inherited predecessor evidence; and
- explicit, claim-bound, nonempty validity scope for any shared evidence reuse.

`ArchitectureRealization.v` proves that, when the concrete bridge reports provider-side instance and realization revisions as the encodings of the architecture-derived values, those Certified provider invariants imply exact architecture-instance preservation and changed architecture realization. A topology-changing pair cannot validate as provider replacement.

## Correspondence boundary

The Rocq theorem intentionally does not certify concrete revision bytes or artifact truth.

Explicit implementation/correspondence boundaries remain:

- `Text`-backed semantic keys and revisions;
- `Map`/`Set` canonicalization and `SemanticForm` serialization;
- digest/collision assumptions;
- construction of exact qualification claim/evidence/admission identities;
- selected artifact identity and runtime ABI truth;
- the concrete encoding bridge between typed architecture revisions and provider-replacement revision tokens;
- source elaboration and build-profile selection; and
- Systems/StageContract regeneration after a realization replacement.

This is build-time substitution, not live provider migration.

## Executable pressure

The unchanged `test/Phase1ArchitectureProviderReplacementMain.hs` corpus supplies nine ARCH-010 cases:

1. independently described implementations expose the same abstract interface and distinct definitions;
2. provider replacement preserves the exact architecture instance;
3. selected implementation replacement changes the architecture realization;
4. the derived replacement pair is accepted;
5. the checker reports exact architecture-derived instance and realization revisions;
6. qualification/evidence/admission lineage changes;
7. an identical selected realization rebuild is deterministic;
8. predecessor evidence cannot qualify the replacement claim; and
9. changing abstract architecture topology rejects as something other than provider replacement.

On green, `PHIL-ARCH-REALIZE-001` may advance from `Active / Tested` to `Discharged / Certified`. With ARCH-IMPORT, ARCH-ID, and ARCH-INST already Certified, that completes the ARCH proof tranche; architecture implementation refinement follows before moving to the next semantic family.
