# Phase 1 Systems semantic subject correspondence v1

Status: bounded executable conformance slice for `SYS-004`.

## Purpose

The Phase 1 Systems/StageContract boundary must preserve semantic subject identity explicitly. Runtime values, owners, borrowed views, storage identities, pointers, handles, and backend representations may participate in realizing or observing a source subject, but none of those implementation identities creates semantic subject correspondence by coincidence.

The governing rule is:

> Equal representation is not equal semantic subject.

This slice composes with the generic SYS-001 StageContract envelope. `SubjectStageBundle` binds the exact base `Phase1StageContractRevision` to an exact map of source semantic subjects and their Systems correspondences, and derives a new canonical subject-stage revision. The base SYS-001 verifier runs first.

## Correspondence shape

A `SubjectCorrespondence` records:

- exact `SourceSubjectKey`;
- one or more exact `SystemsValueRef` values, each naming both function and `ValueId`;
- an exact accepted relation revision;
- an exact validity-scope revision; and
- zero or more evidence references.

A single stable subject may legitimately correspond to several Systems values. For example, an owned byte object and scoped borrowed views of that owner may all participate in one correspondence when the named relation establishes that the views observe the same stable subject.

The relation is one-to-many in that direction. In this bounded SYS-004 model, one exact Systems value may not simultaneously be the realization of two distinct stable source subjects. More general aggregate or packed-representation relations, if needed later, must be introduced explicitly rather than inferred from representation sharing.

## Runtime coincidence is represented only to reject it

`RuntimeRepresentationCoincidence` is an explicit invalid correspondence basis. It captures attempted arguments such as:

- same pointer;
- same storage identity;
- same allocation address;
- same backend handle;
- same runtime bytes; or
- same representation/layout.

The verifier rejects this basis even when all referenced Systems values exist.

A checked correspondence instead uses `CheckedSubjectRelation relation_revision`, whose exact semantic meaning and evidence lineage remain separately inspectable.

## Exact Systems references

`SystemsValueRef` contains both the Systems function key and `ValueId`. The verifier rejects:

- unknown functions;
- unknown values within an existing function;
- empty Systems-value sets; and
- reuse of one exact Systems value for two different source subjects.

This avoids accidentally treating value spelling, storage identity, or globally similar names as subject identity.

## Witness pressure

### Framed upload

The server payload subject corresponds explicitly to:

- the owning `server.payload` Systems value; and
- its `server.payload_view` borrowed observation.

The relation cites the upload payload owner/borrow validity scope and the existing exact-receive/shared-borrow facts.

### Steve

Steve carries two distinct byte-object subjects in this slice:

- candidate bytes in `StevePut`, with digest/install borrowed views; and
- read-result bytes in `SteveGet`, with the digest-check borrowed view.

The two correspondences remain distinct even if their concrete `systemsStorageIdentity` fields are deliberately made equal in a mutation fixture.

## Conformance corpus

The dedicated harness checks:

1. framed upload correspondence acceptance;
2. Steve correspondence acceptance by the same verifier;
3. acceptance when two distinct subject owners happen to carry the same concrete storage identity;
4. rejection when correspondence for one equal-storage subject attempts to reuse the other subject's exact Systems value;
5. rejection of runtime pointer/storage/byte coincidence as a correspondence basis;
6. rejection of an unknown Systems value;
7. rejection when one exact Systems value is assigned to two stable subjects; and
8. canonical subject-stage identity independent of map enumeration order.

## Boundaries

This slice establishes subject identity correspondence only. It does not yet prove provider-call/admission correspondence (`SYS-005`), authority/effect refinement, branch-sensitive resource/failure preservation, protocol/boundary relations, evidence-copy transfer, carrier coverage, erasure, target strengthening, or cost/deployment relations.

Those later relations may cite these exact subject keys and Systems references rather than reconstructing subject identity from runtime representation.
