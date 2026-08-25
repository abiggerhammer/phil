# Phase 1 callable transition boundary v1

Status: implementation note for the CALL-006--009 tranche.

This slice extends the callable/closure substrate with exact first-class callable ownership occurrences and checked callee transitions.

## Governing rule

A callable contract governs invocation, but availability belongs to an exact callable ownership occurrence. Equal callable contracts do not identify equal callable values.

The checker therefore tracks a `CallableOccurrenceKey` separately from the callable contract revision.

## PreserveCallee

`PreserveCallee` leaves the exact predecessor callable occurrence available after a continuing invocation. For a closure with moved affine/linear captures, the callable-body/resource checker must report the exact same restricted capture identities in the post-body residue. Missing restricted state rejects the preserving transition.

A preserved linear closure remains linear: repeated invocation is permitted only as repeated use of the same unique owner, never by contraction or copying.

## ConsumeCallee

`ConsumeCallee` removes the predecessor callable occurrence. A later invocation through the stale predecessor key rejects as unavailable.

This v1 transition checker assumes ordinary callable-body/resource checking has already justified what happens to captured resources and results; it does not by itself certify their complete redistribution.

## ReplaceCallee

`ReplaceCallee` consumes the predecessor and requires one explicit distinct successor occurrence. The successor must match the exact declared callable interface revision and explicit callable state key. The predecessor key cannot be reused for the successor, and a successor key already live in resource state rejects.

The successor may intentionally have the same public callable interface as the predecessor. That does not resurrect the predecessor: occurrence identity and contract identity remain separate.

## Conformance

`test/Phase1CallableTransitionsMain.hs` covers CALL-006 through CALL-009, including repeated preserving invocation, missing preserve residue, one-shot stale reuse, equal-interface replacement, predecessor-key resurrection, and successor interface/state mismatch.

The harness runs as a named step inside the shared Haskell `build-and-test` CI job.

## Still deferred

This slice does not claim complete per-outcome resource redistribution, source callable syntax, authority/evidence checking, scoped-loan closure escape, public effect-bound refinement, higher-order callable refinement, recursion, provider/foreign qualification, closure conversion, or Rocq proof.
