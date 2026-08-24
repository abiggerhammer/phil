# Phase 0 CI baseline

Phase 0 is frozen at merge commit:

```text
911f6f73d9fd7c788f081fe616ad640b83fb882e
```

That commit contains the merged `PHIL-PHASE0-CERT-001` closure tranche for the frozen upload reference program.

## Purpose

Phase 0 was built incrementally. Its GitHub Actions directory therefore records the construction history as many per-slice semantic, runtime, proof, back-certification, and certification workflows.

That history is valuable, but it is not the desired Phase 1 regression surface.

The CI normalization is intentionally split into two tranches.

### Tranche A: equivalence

Add normalized repo-local runners and a consolidated Phase 0 baseline workflow while retaining every existing Phase 0 workflow unchanged.

The candidate baseline currently exposes two end-to-end regression gates:

- frozen source-to-Systems projection;
- frozen source-bound LLVM plus complete runtime ABI checking and integrated native execution.

The native gate requires the exact frozen source-pair digest:

```text
5339e6c7e6520e5495c1d304edcc2427e4bdbe19ce80167af3a314ab2f69e4df
```

and executes the accepted-upload, digest-rejection, and client-cancellation scenarios through the same checked-in source, emitter, runtime providers, ABI checker, LLVM/Clang 18 tool boundary, and native fixture used to close Phase 0.

No theorem statement, obligation ID, certificate format, runtime profile, test fixture, negative case, or implementation behavior is changed by this tranche.

The old and new gates must be green on the same tree before any legacy workflow is retired.

### Tranche B: normalization

After equivalence is established:

1. retain ordinary build/test CI as the fast default gate;
2. normalize the active Rocq corpus and proof/correspondence checks into a coherent proof gate;
3. retain the consolidated frozen Phase 0 regression gate;
4. retain content-bound certification as a separately attributable, path-filtered gate;
5. retire redundant per-slice construction workflows from `main` while preserving them permanently in Git history at the Phase 0 freeze.

## Rule for the refactor

This is orchestration cleanup, not assurance redesign.

Any change that alters a claim, theorem, obligation revision, certificate, validity scope, runtime ABI/profile, fixture semantics, or expected observation belongs in a separate semantic or assurance tranche and must not be smuggled into CI normalization.
