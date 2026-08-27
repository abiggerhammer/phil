# Phase 1 data subject transport v1

Status: implementation slice for `PHIL-DATA-SUBJECT-001` / `DATA-012`.

## Purpose

Evidence in Phil is proposition- and subject-specific. A consume-and-reconstruct update therefore cannot silently retarget evidence from a stable semantic subject `κ` to a replacement subject `κ2` merely because the two values have the same type, stable-id kind, bytes, pointer, object slot, handle, or runtime representation.

This slice introduces an explicit Core checker for that boundary.

## Subject-bound evidence

`SubjectBoundEvidence` records:

- one evidence reference;
- one distinguished subject binder;
- one proposition template containing that binder; and
- the exact stable semantic subject to which the evidence currently applies.

The concrete proposition is produced only by substituting the exact subject identity for the distinguished binder and normalizing the result.

A subject-bound template that does not mention its declared subject binder is rejected by this checker. Contract-level or otherwise subject-independent evidence belongs outside this DATA-012 transport path.

## Consume and reconstruct

`DataSubjectUpdate` records:

- the predecessor subject;
- the replacement subject;
- that the predecessor restricted value was consumed; and
- that the replacement restricted value was constructed.

Both lifecycle facts are required. This checker does not infer them from pointer reuse, an SSA assignment, equal bytes, or a matching runtime type.

Subjects must carry an explicitly known `StableId[K]` sort and predecessor/replacement must use the same stable-id kind. Equal kinds do not imply equal identities.

Representation tokens are deliberately nonsemantic metadata. They may record a pointer, handle, object slot, SSA name, or other lower-stage observation, but the checker never uses them to establish semantic subject identity or transport.

## Same subject

If predecessor and replacement have the exact same semantic stable identity, no proposition retargeting occurs and no transport witness is required. Representation metadata may change without changing semantic subject identity.

Supplying a transport witness for the same semantic subject is rejected as spurious: DATA-012 transport exists to justify a genuine change of semantic subject.

Validity changes caused by mutation of one continuing stable subject remain a separate validity-contract question; this slice only governs semantic subject identity and succession.

## Different subject

If the semantic identity changes from `κ` to `κ2`, evidence remains pinned to `κ` by default. The update is rejected unless it supplies a `DataSubjectTransport` whose accepted relation binds all of:

- a nonempty relation/validity revision;
- the exact evidence reference;
- exact predecessor subject `κ`;
- exact replacement subject `κ2`;
- the exact source proposition instantiated at `κ`; and
- the exact target proposition obtained by instantiating the same subject template at `κ2`.

The transport may be classified as a copy or succession relation. This implementation does not infer the truth of the relation from that label: acceptance of the relation remains explicit evidence/assurance input.

Rejected relations, empty relation revisions, mismatched evidence, wrong source/target subjects, or wrong source/target propositions all fail closed.

## Conformance pressure

The `DATA-012` corpus covers:

- same-subject preservation without transport;
- distinct-subject rejection without transport;
- exact accepted succession transport;
- same stable-id kind being insufficient;
- same representation token being insufficient;
- wrong predecessor/replacement bindings;
- wrong evidence reference;
- wrong source/target propositions;
- rejected or scope-less transport evidence;
- missing predecessor consumption or replacement construction;
- evidence initially bound to the wrong predecessor;
- stable-id-kind mismatch;
- non-stable subject identity;
- a purported subject-bound template that does not mention the subject; and
- rejection of a spurious transport on an unchanged semantic subject.

The Steve pressure shape uses the same form as `DigestMatches(id, object)`: `id` remains an independent proposition parameter while only the distinguished stable object subject may move through an explicit succession relation.

## Boundaries

This slice does not prove:

- truth of a copy/succession relation;
- evidence validity after mutation of the same stable subject;
- pointer/SSA/object correspondence between Core subjects and lower stages;
- boundary-layout or zero-copy subject transfer (`PHIL-BND-SUBJECT-001`);
- Systems subject correspondence (`PHIL-SYS-SUBJECT-AUTH-001`); or
- provider-specific proposition truth.

It also does not globally rewrite `dischargeProposition`. DATA-012 is introduced as an explicit standalone Core checker first so the succession semantics can be tested and later certified before broader integration.
