# Phase 1 Systems evidence subject transfer v1

Status: bounded executable conformance slice for `SYS-011`.

## Governing rule

Evidence is indexed by an exact stable semantic subject. Creating, copying, staging, receiving, or otherwise materializing a distinct subject does not retarget evidence from the old subject merely because the two objects currently contain equal bytes or share a runtime representation.

For a source subject `κ1` and a distinct target subject `κ2`, evidence may be rebound only through an explicit accepted relation that identifies:

1. the exact subject-copy/transfer relation;
2. the exact byte-equality relation relevant to the transfer;
3. the exact proposition-transfer law establishing which evidence remains valid on `κ2`; and
4. the validity scope of that relation.

In shorthand:

```text
evidence[P, κ1]
+ checked copy/transfer(κ1, κ2)
+ exact byte equality(κ1, κ2)
+ transfer law for P
-> evidence[P, κ2]
```

Runtime pointer equality, allocation reuse, matching storage identifiers, matching target types, matching byte lengths, or a successful unrelated operation are not substitutes for this relation.

## Relation and rebinding are separate objects

`SubjectTransferRelation` records the checked semantic relation between two exact `SourceSubjectKey`s.

`EvidenceRebindingClaim` records an attempt to transport one or more exact evidence references from the source subject to the target subject.

Keeping these separate is deliberate. A copy relation does not mean that every proposition about the source object is transportable. The relation contains an explicit `subjectTransferAllowedEvidence` set, and a rebinding claim succeeds only when every requested evidence reference is in that set.

This makes proposition competence mechanical:

- the source must actually possess the named evidence;
- a registered transfer relation must exist;
- that relation must name exactly the same source and target subjects; and
- the relation must explicitly permit transfer of that evidence.

## Checked basis

The bounded checked basis is:

```text
CheckedSubjectCopy
    CopyRelationRevision
    ByteEqualityRevision
    EvidenceTransferLawRevision
```

All three revisions are independent semantic inputs.

- `CopyRelationRevision` identifies what concrete copy/staging/transfer relation is being relied upon.
- `ByteEqualityRevision` identifies the exact equality fact established between the old and new byte subjects.
- `EvidenceTransferLawRevision` identifies the proposition-specific rule saying why the named evidence survives this change of subject.

`RuntimeSubjectCoincidence` exists only as a rejected constructor so the invalid inference is represented explicitly in the conformance corpus.

## Subject authority

SYS-011 reuses the subject graph established by SYS-004. Both source and target must already be distinct registered `SourceSubjectKey`s in the same checked subject stage.

The transfer layer therefore does not invent semantic subjects from target pointers or buffers. It only states a checked relation between subjects whose target representations are already known.

## Real upload pressure case

After SYS-010, upload has two intentionally distinct payload subjects:

```text
upload.payload.client
    -> UploadClient:client.payload

upload.payload.server
    -> UploadServer:server.payload
       UploadServer:server.payload_view
```

The client subject carries `payload.exact_send`; the server subject carries `payload.exact_receive` and `digest.shared_borrow`.

SYS-011 deliberately tests the invalid attempt:

```text
payload.exact_send[upload.payload.client]
    -> payload.exact_send[upload.payload.server]
```

with no accepted subject-transfer relation. It is rejected.

This is stronger than byte equality. Even if the protocol transported corresponding payload bytes, sender-side send evidence is not automatically receiver-side evidence about a distinct subject.

## Real Steve pressure case

Steve has two distinct stable subjects:

```text
steve.bytes.candidate
steve.bytes.read-result
```

The candidate subject carries `steve.blob.borrow-preservation`; the ordinary read-result subject does not.

SYS-011 tests the invalid attempt to rebind that candidate-specific evidence to the read-result subject without an accepted transfer relation. It is rejected.

The conformance corpus also includes one explicitly synthetic checked-copy fixture between those subjects. That fixture exists only to prove that the positive mechanism works when an exact copy/equality/transfer-law relation is supplied; it is not a claim about ordinary Steve execution.

## Failure distinctions

The verifier distinguishes:

- source or target subject absent;
- source and target accidentally identical;
- source never possessed the named evidence;
- no transfer relation supplied;
- supplied relation absent from the registry;
- supplied relation names different endpoints;
- relation exists but is not competent to transfer this proposition;
- relation revisions or validity scope are empty; and
- runtime representation coincidence presented as semantic correspondence.

These are separate diagnostics because they correspond to separate assurance failures.

## Deterministic identity

The SYS-011 stage revision binds:

- the exact SYS-004 subject-stage revision;
- the exact set of subject-transfer relations; and
- the exact set of evidence-rebinding claims.

Semantically unordered maps and sets are canonicalized before identity derivation. Traversal or insertion order therefore cannot change the stage revision.

## Deferred

This slice intentionally does not yet implement:

- evidence erasure after completed proof work (`SYS-012`);
- assumption laundering rejection (`SYS-013`);
- target strengthening and derived realization obligations (`SYS-014`);
- runtime carrier multiplicity;
- staging cost attribution;
- next-stage ABI requirements;
- arbitrary transitive evidence-transfer chains; or
- final compact semantic digests.

A later extension may support chains of checked subject transfers, but each hop must preserve the same rule: evidence moves only through a competent explicit relation for the exact proposition being transferred.
