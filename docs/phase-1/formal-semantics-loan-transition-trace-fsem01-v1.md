# FSEM-01 — concrete production loan-state checkpoints (bounded v1)

> **Status: executable production checker observation, not a source-to-Rocq
> simulation theorem or a new normative language rule.** Tracks
> [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613) and the
> [proposed correspondence](formal-semantics-loan-state-correspondence-fsem01-v0.md)
> merged in #1625. The trace API is deliberately restricted to the
> [admitted FSEM-01 Grammar-v1 bridge](formal-semantics-borrow-resource-bridge-fsem01-v1.md).

## Purpose and actual instrumentation boundary

The ordinary checker in [`Engine.hs`](../../src/Phil/Surface/Check/Engine.hs)
continues to run `evalBorrow` for every borrow. `evalBorrow` now delegates to
`evalBorrowTraced` and discards the observation checkpoints. The bounded
`traceSurfaceBorrowComponent` entry point invokes **that same evaluator**
for a synthetic component consisting of exactly one borrow-expression
statement followed by one return. This deliberately avoids a second
implementation of `startSharedLoan`, `endSharedLoan`, or the escape test.

`BorrowTraceRun` carries:

- `traceOutcome :: Either SurfaceCheckError SurfaceCheckResult`: the
  production checker outcome (including the exact `BorrowEscape` class and
  diagnostic on the negative).
- `traceCheckpoints :: [BorrowTraceCheckpoint]`: ordered snapshots, even
  when `traceOutcome` is `Left`. Each snapshot holds the phase, the exact
  owner and view `Core.Name` values, and **actual**
  `ResourceContext.linearBindings` and `ResourceContext.sharedLoans`.
  These are concrete production states, not predicted membership bits.

The source-facing
[`grammarV1CheckedBorrowResourceFunctionTrace`](../../src/Phil/Surface/GrammarV1/BorrowResourceSurface.hs)
uses precisely the same bounded source projection and type/binder evidence
as `grammarV1CheckedBorrowResourceFunction`. It returns
`Nothing` for unsupported source shapes, `Just (Left ...)` for errors
before a projected checker run, or `Just (Right trace)` after an admitted
projection—including one whose production outcome is a rejection. The
trace attaches both resolved source binder records, whose declaration-rooted
keys can be checked against the generated `Core.Name`s in the snapshots.
No source spelling or inferred global owner is used as a resource identity.

## Exact paired controls

Both source functions have the same exact `Bytes[8]` parameter and result
type, the same owner identity and the same outer return:

~~~phil
fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {
  borrow owner as view { view; unit; };
  return owner;
}
~~~

~~~phil
fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {
  borrow owner as view { view; };
  return owner;
}
~~~

For a generated owner `o`, with `T = TyBytes (RefNat 8)`:

| Positive phase | `linearBindings[o]` | `o ∈ sharedLoans` | Meaning |
| --- | --- | --- | --- |
| `TraceBeforeLoan` | `Just T` | No | Parameter installed and not yet borrowed |
| `TraceLoanStarted` | `Just T` | Yes | Actual `startSharedLoan` succeeded |
| `TraceBodyResult False` | `Just T` | Yes | Last borrow body value is Unit, so no view escapes |
| `TraceLoanClosed` | `Just T` | No | Actual `endSharedLoan` succeeded |
| `TraceOwnerReturned` | `Nothing` | No | Outer return consumed the original linear owner |

The escaping-view negative instead ends with
`TraceBodyResult True, TraceEscapeRejected`. **At rejection**, the
original linear owner remains present and its shared loan remains active.
There is **no** `TraceLoanClosed` and **no** `TraceOwnerReturned`
checkpoint. The error is exactly production `BorrowEscape` with detail
`shared view escapes its lexical scope` rather than a type mismatch.
The rejected path is *not* a successful continuing or terminal state.

## Checks and evidence

[`Phase1FSEM01BorrowResourceTraceMain.hs`](../../test/Phase1FSEM01BorrowResourceTraceMain.hs)
checks:

1. Exact owner/view generated Core names and distinct source binder keys
   persist at each checkpoint.
2. Positive cut ordering and exact linear-owner/loan-membership changes for
   both a Unit-only body and `view; unit;`.
3. Rejected cut ordering, error class and detail, with an open loan and
   still-present owner at the last observable checkpoint.
4. **Behavioral parity** between
   `grammarV1CheckedBorrowResourceFunction` and the traced entry point,
   including both positives, the negative, unsupported `U8`, unknown
   local owner and shadowed view. Unsupported cases must not fabricate trace
   events.
5. CI emits the trace checkpoints in the dedicated workflow log for
   review, but those logs are **not** a separately certified proof object.

Replay with:

~~~sh
cabal build all --enable-tests
cabal exec -- runghc -Wall -Werror -isrc test/Phase1FSEM01BorrowResourceTraceMain.hs
~~~

The [borrow-view workflow](../../.github/workflows/phase1-surface-borrow-view-scope-proofs.yml)
strictly typechecks the test and executes it. Acceptance must be evaluated
on the **exact PR head**, without relying on previous passing runs.

## Explicit limits and next correspondence obligation

The observer only supports a two-statement synthetic component with a
single borrow and return. It does not observe a general Grammar-v1 program,
prove a source operational relation, discharge `satisfies C`, or certify
effectful paths, joins, loops, captures, nested borrows, arbitrary aliases or
the compiler's full behavior. A checker failure during a more complex
borrow body may produce a *prefix* of checkpoints, not a total trace; no
post-error state is fabricated. The observation format is specific to
production `Core.Name`/`Ty`/`ResourceContext`, **not** a generated Rocq
`ResourceOwner := nat` encoding.

In particular,
[`ResourceScope.v`](../../proof/Phil/Core/ResourceScope.v) proves that
normalized **continuing joins and loop backedges** do not carry live loans.
It does not prove that a Grammar-v1 borrow exit corresponds to that
relation, nor that the checker preserves its abstract loan membership.
The next proof needs an exact owner-ID encoding, a state relation, and
transition/error simulation over these now-observable production states.
Terminal return must not be reclassified as a continuing boundary.

This PR does **not** mark the source-to-model simulation obligation
discharged in the Logic Ledger or Conformance Matrix.
