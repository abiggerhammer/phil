# Steve surface architecture sketch

Steve is the first independently motivated non-upload pressure test for the Phil surface language. Steve 0 is a local append-only content-addressed byte store with two operations: `put` and `get`.

The normative Steve design material lives in the durable research corpus. This directory is intentionally checker-facing: it records the smallest plausible `.phil` witness we can write against the current language and makes any mismatch between that witness and the implemented checker concrete.

## Branch policy

Steve remains on the `steve/architecture-sketch` branch while the design and checker-facing witness mature. Do not merge it to `main` or open a handoff PR merely to expose intermediate work. The branch should periodically incorporate relevant `main` changes from the independently advancing Haskell implementation and Rocq proof tracks, and its CI should remain green against the code it actually contains.

The intended external handoff point is a coherent Steve package: design notes and obligations agree with the checker-facing witness, the witness parses in CI, known semantic checker gaps are explicitly classified, and the material is ready to present rather than merely ready to discuss.

## Intended architectural boundary

Steve depends on two authorities:

- `DigestProvider[SHA256]`: compute a content ID over an immutable byte view and check whether a byte view matches a supplied content ID.
- `BlobProvider`: read by content ID and atomically install bytes if and only if the ID is currently absent.

Steve itself should receive no overwrite or delete authority.

The important ownership choice exposed by the first sketch is that `blob_install_if_absent` must observe a borrowed read-only view of the candidate bytes rather than consume them. On the `already_exists` path Steve must still own the candidate so it can compare it byte-for-byte with the existing object and distinguish idempotent reuse from a digest collision.

## What the current sketch is testing

`steve.phil` deliberately uses only syntax already accepted by the Phase 0 parser: components, typed parameters, named opaque types, `OwnedBytes[n]`, borrowing, primitive calls, decisions, construction, release, and return.

Branch CI runs:

```text
cabal run phil-core -- parse examples/steve/steve.phil
```

This is intentionally only a syntax gate. It must not be described as semantic acceptance of Steve.

It is not yet expected to pass whole-component semantic checking. In particular it exposes these pressure points:

1. **Provider interfaces are not source declarations yet.** The current surface can pass provider authority as typed component parameters, but provider operations must still appear as free primitive calls taking the authority explicitly.
2. **A reusable multi-operation provider is not directly expressible.** `StevePut` and `SteveGet` are separate components because the current surface has no declaration form for a `Store` provider exposing several operations.
3. **Generic decision/result types are not yet checker-defined.** The upload checker knows a fixed set of primitive decision shapes. Steve needs ordinary result variants such as `installed`, `already_exists`, `found`, and `storage_failure`.
4. **Linear ownership inside result constructors needs a general rule.** `GetOk` transfers owned bytes to the caller. The checker must preserve that ownership through a sum/record result rather than treating the constructed value as an opaque unrestricted scalar.
5. **Opaque claim/validator bindings are still architecture-environment data.** Steve needs `DigestMatches(ContentId, byte-view)` tied specifically to `DigestProvider`, without granting arbitrary code authority to manufacture that evidence.

## Classification against accepted Phil decisions

The first pass does **not** reveal a need for Phil ADR-012.

- The borrowed candidate rule is already covered by ADR-002 shared loans and ADR-005's requirement that operation arms state their resource transitions. Steve ADR-002 merely specializes those semantics to `BlobProvider.installIfAbsent`.
- Provider operation contracts already belong in ADR-001's immutable static signature `Σ`. Source-level provider/member declarations are therefore an elaboration/surface implementation gap, not a new Core semantic decision.
- ADR-001 already permits a component to provide an ordinary result type or another declared interface. A multi-operation `Store` interface therefore needs source/checker realization, not a new semantic foundation.
- ADR-001 explicitly says that returning an owning value transfers its ownership into the declared result, while ADR-005 requires per-arm resource accounting. Generic sum/record results carrying linear fields are therefore missing checker machinery, not an unresolved ownership rule.
- ADR-006 already defines opaque claims and declared competent evidence producers, including runtime validators over shared loans. Generalizing `DigestMatches` beyond the upload-specific environment is implementation of that accepted decision.

The right next implementation target is thus a more general architecture/static-signature surface and generic checked result shapes. A new Phil ADR should be proposed only if implementing those accepted rules forces an actual choice not already fixed by ADR-001/002/005/006.

## Steve 0 claims exercised by the sketch

- successful `put` returns an ID matching the candidate bytes;
- publication never overwrites an existing object;
- repeated `put` of identical bytes succeeds idempotently;
- an existing object with the wrong digest is reported as corruption;
- distinct bytes with the same valid digest are reported as a digest collision;
- successful `get` returns bytes only after digest verification;
- integrity failure is distinct from absence;
- failed/interrupted publication does not authorize a partial object as committed.
