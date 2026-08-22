# Steve surface architecture sketch

Steve is the first independently motivated non-upload pressure test for the Phil surface language. Steve 0 is a local append-only content-addressed byte store with two operations: `put` and `get`.

The normative Steve design material lives in the durable research corpus. This directory is intentionally checker-facing: it records the smallest plausible `.phil` witness we can write against the current language and makes any mismatch between that witness and the implemented checker concrete.

## Intended architectural boundary

Steve depends on two authorities:

- `DigestProvider[SHA256]`: compute a content ID over an immutable byte view and check whether a byte view matches a supplied content ID.
- `BlobProvider`: read by content ID and atomically install bytes if and only if the ID is currently absent.

Steve itself should receive no overwrite or delete authority.

The important ownership choice exposed by the first sketch is that `blob_install_if_absent` must observe a borrowed read-only view of the candidate bytes rather than consume them. On the `already_exists` path Steve must still own the candidate so it can compare it byte-for-byte with the existing object and distinguish idempotent reuse from a digest collision.

## What the current sketch is testing

`steve.phil` deliberately uses only syntax already accepted by the Phase 0 parser: components, typed parameters, named opaque types, `OwnedBytes[n]`, borrowing, primitive calls, decisions, construction, release, and return.

It is not yet expected to pass whole-component semantic checking. In particular it exposes these pressure points:

1. **Provider interfaces are not source declarations yet.** The current surface can pass provider authority as typed component parameters, but provider operations must still appear as free primitive calls taking the authority explicitly.
2. **A reusable multi-operation provider is not directly expressible.** `StevePut` and `SteveGet` are separate components because the current surface has no declaration form for a `Store` provider exposing several operations.
3. **Generic decision/result types are not yet checker-defined.** The upload checker knows a fixed set of primitive decision shapes. Steve needs ordinary result variants such as `installed`, `already_exists`, `found`, and `storage_failure`.
4. **Linear ownership inside result constructors needs a general rule.** `GetOk` transfers owned bytes to the caller. The checker must preserve that ownership through a sum/record result rather than treating the constructed value as an opaque unrestricted scalar.
5. **Opaque claim/validator bindings are still architecture-environment data.** Steve needs `DigestMatches(ContentId, byte-view)` tied specifically to `DigestProvider`, without granting arbitrary code authority to manufacture that evidence.

None of these observations by itself requires a new Phil ADR. The immediate task is to determine which are missing implementations of already-accepted architecture and which, if any, force a new language-level decision.

## Steve 0 claims exercised by the sketch

- successful `put` returns an ID matching the candidate bytes;
- publication never overwrites an existing object;
- repeated `put` of identical bytes succeeds idempotently;
- an existing object with the wrong digest is reported as corruption;
- distinct bytes with the same valid digest are reported as a digest collision;
- successful `get` returns bytes only after digest verification;
- integrity failure is distinct from absence;
- failed/interrupted publication does not authorize a partial object as committed.
