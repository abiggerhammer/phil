# Phase 0 recognition failure detail v1

## Scope

This semantic successor preserves the failure detail carried by the frozen upload source when `Hello` or `Begin` recognition rejects input.

The accepted source has the shape:

```text
decide recognition {
  rejected(reason) => fail recognition(reason) on pending
  accepted(parsed) => ...
}
```

The predecessor Systems candidate preserved the success/failure control split and cleanup obligations but represented failure only by a dedicated CFG edge and fatal class. The `reason` identity was absent.

This tranche restores that semantic information without selecting a physical reason representation or runtime diagnostic ABI.

## Failure-only values

The successor introduces two distinct values:

```text
server.hello_recognition_reason : RuntimeOpaque[RecognitionReason[Hello]]
server.begin_recognition_reason : RuntimeOpaque[RecognitionReason[Begin]]
```

They are intentionally grammar-specific and are not interchangeable.

## Hello failure flow

On the exact `Hello` recognition-failure edge:

```text
materialize recognition failure reason Hello(
  server.pending.hello)
  -> server.hello_recognition_reason

fail recognition Hello(
  server.pending.hello,
  server.hello_recognition_reason)

destroy pending/frame(server.pending.hello, server.frame.hello)
fatal RecognitionFailure[Hello]
```

The reason has exactly one semantic observation: forwarding into the fatal recognition effect.

## Begin failure flow

Likewise, on the exact `Begin` recognition-failure edge:

```text
materialize recognition failure reason Begin(
  server.pending.begin)
  -> server.begin_recognition_reason

fail recognition Begin(
  server.pending.begin,
  server.begin_recognition_reason)

destroy pending/frame(server.pending.begin, server.frame.begin)
fatal RecognitionFailure[Begin]
```

The reason again has exactly one semantic observation.

## Why `TermRecognize` stays specialized

This change does not rewrite recognition into a generic runtime choice. `TermRecognize` already captures a stronger semantic boundary:

- exact pending-ingress identity;
- exact raw-view identity;
- recognition runtime site;
- success path that may commit the pending ingress;
- failure path that must destroy it.

The failure detail is therefore materialized on the dedicated failure edge, symmetrically with the existing success-side materialization of recognized records.

## Cleanup

Existing cleanup semantics are preserved exactly. The same pending owner and frame owner are destroyed on failure, and the fatal class remains grammar-specific.

The semantic forwarding effect does not choose whether a future physical runtime reports, logs, stores, or otherwise encodes the detail. Those are target decisions.

## Lowering decision

`lower.recognition.failure_detail` records the semantic materialization of both failure-only reason identities and their exact forwarding relation.

Its runtime residue explicitly leaves open:

- concrete reason representation;
- recognizer/provider error object lifetime;
- physical fatal-diagnostic effect ABI;
- formatting/logging policy.

## Assurance boundary

Existing recognition runtime evidence continues to justify the recognition gate itself. This semantic successor changes the Systems artifact digest; no previously content-bound LLVM translation certificate is broadened by this change.

A later backend tranche must explicitly lower the failure reason and fatal effect before claiming a physical recognition-failure ABI.
