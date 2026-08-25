# Phase 1 Steve provider qualifications v1

Status: executable witness materialization for `PROV-016`.

## Purpose

`PROV-016` is the first provider-qualification case that stops using only synthetic provider fixtures and materializes the two provider contracts Steve actually depends on:

- `DigestProvider[SHA256]`;
- `BlobProvider`.

The witness-specific materializer lives under `Phil.Examples.Steve`, not `Phil.Core`. It constructs provider-specific contracts, relations, conditions, and evidence, then feeds them through the generic Phase 1 provider checkers. Core has no `Steve` dispatch path.

Both providers produce the same `SteveProviderQualificationArtifact` schema. Optional whole-provider layers are populated only when the public provider semantics require them.

## DigestProvider[SHA256]

The digest qualification materializes:

- exact provider interface and implementation revisions;
- explicit `compute` and `check` operation correspondences;
- exact per-outcome resource residues in which the input bytes remain borrowed rather than consumed;
- exact SHA-256 semantic effect surfaces;
- evidence-producer competence for `DigestMatches(id, object)`;
- a scoped borrowed byte observation mapped to the stable owned byte-object subject;
- exact proposition parameterization in which `id` remains a proposition parameter rather than being folded into subject identity;
- a stable-owner validity contract; and
- an authority inventory exposing no storage/publication authority through the digest provider surface.

The SHA-256 semantic profile remains an explicit Phase 1 assumption in this pressure artifact rather than being silently promoted to a cryptographic proof.

## BlobProvider

The blob qualification materializes:

- exact `read` and `install-if-absent` operation correspondences;
- `read` outcomes `found`, `not-found`, and `storage-failure`;
- install outcomes `installed`, `already-exists`, and `storage-failure`;
- candidate-byte resource residues showing that every install outcome borrows Steve's owner rather than consuming it;
- a bounded abstract/implementation state simulation for absent versus complete-present object state;
- a public-history `no-replace` law;
- lifecycle/interruption points before and after publication;
- an observation boundary at which publication may expose only `object.absent` or `object.complete-and-correct`, never a partial object;
- cleanup/retry behavior for both lifecycle points;
- a narrow public authority surface (`read`, `install-if-absent`) over a broader backing authority inventory that also contains overwrite/delete;
- explicit assumption-dependent dispositions for the broader overwrite/delete authority;
- explicit no-out-of-band-mutation, atomic no-replace publication, confinement, and complete-copy-before-borrow-end conditions.

The lifecycle and resource layers are intentionally separate. Normal-return resource checking establishes that the candidate remains a borrow. Lifecycle checking establishes that interruption cannot leave a client-visible partial publication and that cleanup does not leak the borrow.

## Qualification closure

Each witness artifact also materializes the generic claim/evidence/admission identity layers.

The evidence disposition map has an exact domain equal to the provider's declared `steveProviderRequiredObligationKeys`; the conformance corpus rejects any accidental missing or invented obligation at the witness boundary.

Conditions remain visible in all three places where they matter:

1. semantic qualification claim conditions;
2. evidence assumption references;
3. contextual admission condition dispositions.

The pressure policy admits those conditions for this Phase 1 witness. This is conditional qualification, not a claim that every future certified-release profile must accept the same assumptions.

## Important negative pressure cases

The corpus reuses the generic checkers to demonstrate:

- two consecutive implementation-level `installed` outcomes violate the public no-replace law;
- a modeled `object.partially-committed` state at the post-publication interruption point is rejected by lifecycle qualification;
- broader overwrite/delete authority cannot disappear merely because the client interface omits those operations;
- the digest loan/view cannot replace the stable byte-object subject in `DigestMatches`;
- the content id remains a separate proposition parameter;
- neither digest nor blob operations consume Steve's owned candidate merely because they inspect/copy it.

## Relationship to the old Phase 0 Steve baseline

The frozen Phase 0 experiment established that Steve's concrete syntax already parsed, but semantic environment construction was still fixture-specific. That experiment was intentionally closed rather than merged.

`PROV-016` does not revive that fixture-specific path. It instead demonstrates that the generic Phase 1 provider vocabulary can now represent and inspect the two provider qualifications Steve needs.

The next integration tranche is generic ArchitectureRealization / Systems / StageContract construction for the framed-upload and Steve witnesses. At that point the original Steve source can be brought back as a full end-to-end witness without adding a `phase0EnvironmentFor`-style Steve special case.

## Deferred

This slice does not yet:

- merge the old `examples/steve/steve.phil` baseline into `main`;
- construct Steve's complete `ArchitectureInstance` and `ArchitectureRealization`;
- lower Steve through the common SystemsArtifact/StageContract path;
- establish a universal proof of BlobProvider law/lifecycle model completeness;
- prove SHA-256 cryptographic correctness;
- define final provider/qualification source syntax; or
- provide Rocq proofs for the provider qualification stack.
