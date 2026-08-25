# Phase 1 generic Systems / StageContract accounting v1

Status: bounded executable conformance slice for `SYS-001`.

## Purpose

Phase 1 requires framed upload and Steve to cross the Architecture-to-Systems boundary through the same schema and verifier rather than through witness-specific compiler logic.

This slice establishes the first generic StageContract envelope around the existing logical `SystemsArtifact` representation. It does not replace the mature Phase 0 upload verifier, and it does not claim that every finer Systems relation from the full Phase 1 contract is already implemented.

The bounded rule is the bidirectional accounting core:

> Every source responsibility crossing the stage boundary has one exact disposition, and every semantically significant Systems mechanism has one exact reverse justification.

## Four identities

`Phase1StageBundle` keeps separately inspectable:

- exact source `InstanceRevision`;
- exact selected `RealizationRevision`;
- canonical `SystemsArtifactRevision` over the logical Systems artifact; and
- canonical `Phase1StageContractRevision` over the exact I/R/S binding plus the bidirectional accounting relation.

The revisions are static build identities. Runtime launches remain separate occurrences.

## Source responsibilities

For SYS-001, the source-responsibility domain is the exact set of `factTransferId` values already present in the artifact's legacy `StageContract.stageFacts`.

This deliberately reuses the existing framed-upload lowering facts while allowing Steve to supply its provider/architecture facts through the same carrier.

Every source fact must have exactly one `Phase1FactDisposition` entry. The first bounded disposition vocabulary is:

- `Phase1FactRealized systems_refs`;
- `Phase1FactPreserved systems_refs`;
- `Phase1FactExported export_ref`; or
- `Phase1FactAssumptionDependent assumptions inner_disposition`.

A realized/preserved disposition may cite only Systems mechanisms present in the exact target artifact. Assumption dependence must name at least one assumption rather than becoming a generic `assumed` escape hatch.

Later SYS slices will refine the source relation into provider, callable, authority, protocol, boundary, resource/failure, runtime-carrier, erasure, cost, and other exact relation kinds. SYS-001 fixes the closure discipline those refinements must preserve.

## Target mechanisms

SYS-001 conservatively classifies every logical Systems operation and terminator as semantically significant.

`collectSystemsMechanisms` derives stable logical keys from function identity, block identity, operation position/kind, and terminator kind. These are logical Systems identities, not machine addresses or backend symbols.

Every mechanism must have exactly one `SystemsJustification` map entry. A justification may cite:

- source facts;
- selected realization facts;
- exact provider/qualification/admission facts; and
- assumption dependencies.

At least one source, realization, or qualification reason must be present. Assumptions by themselves do not justify the existence of a target mechanism.

This conservative rule can later be narrowed only by introducing an explicit competence boundary for genuinely incidental backend details. Nothing represented in the logical Systems graph may currently remain unexplained.

## Same verifier, two witnesses

The two witness constructors live in `Phil.Examples.Phase1.SystemsWitnesses`.

### Framed upload

The upload witness reuses the existing Phase 0 `SystemsArtifact`, including its real control graph, resource owners/views, runtime sites, lowering decisions, invariants, and stage facts.

The Phase 1 wrapper supplies exact Phase 1 instance/realization identities and indexes the existing source/target responsibilities through the generic accounting envelope.

### Steve

Steve now has a bounded logical Systems graph with `StevePut` and `SteveGet` functions:

- `StevePut` invokes `DigestProvider.compute`, then `BlobProvider.install-if-absent`, and commits the source-visible put event only on the corresponding successful branch;
- `SteveGet` invokes `BlobProvider.read`, then `DigestProvider.check`, and commits the source-visible get event only after the digest check accepts;
- the graph keeps owned byte objects and borrowed provider observation views distinct;
- provider calls are justified by the exact Steve provider admissions materialized in PROV-016; and
- the provider assumptions remain explicit assumption dependencies.

The witness constructor is data-specific, as expected. The verifier is not: both values are passed directly to `verifyPhase1StageBundle`.

There is no witness tag or `case Steve` / `case Upload` dispatch in the verifier.

## Verification procedure

`verifyPhase1StageBundle` checks:

1. verifier-profile identity is explicit;
2. `SystemsArtifactRevision` recomputes exactly;
3. `Phase1StageContractRevision` recomputes exactly;
4. the embedded legacy StageContract still names the exact Systems-program digest;
5. the source-fact set exactly matches the artifact's source responsibility set;
6. the disposition map domain exactly covers that set;
7. the Systems-mechanism set exactly matches the logical artifact;
8. the justification map domain exactly covers every mechanism;
9. every realized/preserved source disposition cites only real target mechanisms;
10. every assumption-dependent disposition names a nonempty assumption set;
11. every target justification cites only real source facts; and
12. every target mechanism has at least one source/realization/qualification justification.

The lowering producer cannot make a missing source fact or unexplained target mechanism disappear by recomputing the outer contract revision: those domains are independently rederived from the Systems artifact.

## Conformance corpus

The dedicated SYS-001 corpus verifies:

- framed upload passes the generic verifier;
- Steve passes the same verifier and same verifier profile;
- their Systems and StageContract revisions remain distinct;
- deleting one source disposition rejects for either witness with the same error family;
- deleting one target justification rejects for either witness with the same error family;
- stale Systems and StageContract revisions reject;
- a source disposition cannot cite a nonexistent target mechanism;
- a target justification cannot cite a nonexistent source fact;
- an empty target justification rejects;
- an empty assumption wrapper rejects; and
- map enumeration order does not alter canonical revisions.

## Deliberate scope boundary

SYS-001 establishes the generic shared **schema + bidirectional closure verifier**, not the complete Systems contract in one PR.

Still to be refined in subsequent SYS cases are the exact typed relations for:

- subject correspondence;
- provider operation/admission linkage;
- callable/closure lowering;
- generic specialization;
- branch-sensitive resource/failure correspondence;
- authority/effect relations;
- protocol/session and boundary representation;
- trace commit-point projection;
- runtime claim/carrier coverage;
- erasure and target strengthening;
- deployment/next-stage requirements; and
- cost attribution.

Those refinements should extend the same envelope rather than create witness-specific lowering pipelines.
