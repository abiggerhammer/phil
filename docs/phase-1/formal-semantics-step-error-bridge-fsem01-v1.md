# FSEM-01 — bounded transition and BorrowEscape error bridge

> **Status:** reviewable, non-normative Rocq model and executable *production*
> observer conformance. It is **not** a universal Haskell-to-Rocq compiler
> simulation theorem or adoption of a Phase 1 language rule. Tracks
> [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613).

## What we now test, beyond identical checkpoint lists

Previous [represented loan checkpoints](formal-semantics-represented-loan-trace-fsem01-v1.md)
from #1635 compared two complete, admissible examples against modeled states.
The new [Rocq step/error bridge](../../proof/Phil/Surface/SurfaceBorrowStepErrorBridge.v)
defines an explicit **event-driven, fail-closed transition interface** for
those same observed phases and owner flags:

| Starting phase | Event | Next phase | Owner present / loan active |
| --- | --- | --- | --- |
| Before loan | Begin | Loan started | Yes / yes |
| Loan started | Body safe | BodyResult(false) | Yes / yes |
| Loan started | Body escapes | BodyResult(true) | Yes / yes |
| BodyResult(false) | Close | Loan closed | Yes / no |
| Loan closed | Return | Owner returned (terminal) | No / no |
| BodyResult(true) | RejectBorrowEscape | Escape rejected (terminal error) | Yes / yes |

All other transitions return `None`. In particular, the rejected state
has **no close, return, or other successor**; the accepted terminal return
also has no successor. The proof distinguishes a terminal error from
a successful terminal owner return.

The model's checked step also demands exact resource-membership bits at
the source checkpoint and preserves the same normalized BinderKey.
Under an explicit `NoDup` catalog, represented binder identity, and
well-formed observation relation, a successful step preserves both
representation and well-formedness. The main theorems are:

- `checked_advance_preserves_owner` and
  `checked_step_preserves_catalog_representation`;
- `checked_advance_is_well_formed`;
- `rejection_cannot_replay_nonempty_suffix` and
  `terminal_return_cannot_replay_nonempty_suffix`;
- `accepted_borrow_step_replay` and
  `rejected_borrow_step_replay` for the admitted event sequences;
- `wrong_branch_cannot_close_escaped_body` and
  `successful_body_cannot_claim_escape_error`;
- `rejection_classifies_only_as_borrow_escape`.

These are *proofs about a model-side observation/checking protocol*,
not theorems about arbitrary Haskell source execution.

## Actual production observation and failure checks

[Phase1FSEM01RepresentedLoanTraceMain.hs](../../test/Phase1FSEM01RepresentedLoanTraceMain.hs)
still runs the actual Grammar-v1 parser and
`grammarV1CheckedBorrowResourceFunctionTrace` on the single-owner
`Bytes[8]` admitted source fragment, across multiple concrete declaration
roots. Alongside the existing exact source-binder/catalog identity,
`Map` linear binding, `Set` active-loan, and ordinary/traced checker
parity controls, it now checks:

1. Every **adjacent pair** of actual source-derived checkpoints admits one
   of the six specified events and the event's resource-state transition.
   An unknown event, changed modeled owner identity, or wrong flag fails.
2. The final phase corresponds to the **actual** production outcome:
   a successful terminal `Bytes[8]` owner return, or the precise
   `BorrowEscape` class and detail
   `shared view escapes its lexical scope`.
3. A real production rejection prefix is deliberately tampered with:
   appended close or return, changed owner key, changed active-loan flag,
   skipped loan-start transition, truncated prefix, and a mismatched
   successful checker outcome must all be **rejected**.
4. The rejected prefix contains the original live owner and active loan;
   the model does **not** report a post-error state or a continuing join.
   Ordinary continuing joins/backedges and terminal return remain separate
   control boundaries.

The [dedicated CI workflow](../../.github/workflows/fsem01-transition-error-bridge.yml)
compiles the entire relevant Rocq proof chain with Rocq 9.2.0, forbids
`Admitted`/new global axioms, and strict-checks/replays the production
Haskell tests using GHC 9.6.7. Only successful CI on the exact final
PR head is evidence for these claims.

## Precise trust boundary and remaining work

- **Not a source operational semantics.** The six event labels are a
  deliberately *bounded* interpretation of snapshots from one
  implementation, not a formal small-step relation for all of Phil.
- **Not an extracted simulation.** The Haskell checker and the Rocq model
  are separately implemented. We test agreement with real checkpoints;
  no extraction/proof forces every Haskell transition to respect the model.
- **Actual diagnostic not proven in Rocq.** Rocq proves rejection has no
  model successor *once labeled rejected*. The Haskell test independently
  verifies the actual failure class, detail, and absence of post-rejection
  checkpoints. The general `containsBorrowedView` and error path remain
  implementation responsibilities outside this proof.
- **Representations still bounded.** The `NoDup` root catalog is an
  observation environment, not a globally stable declaration numbering.
  Unicode Haskell `Text` and Rocq `String` have no proven
  cross-language bijection. Ordinal bounds and general resource-map
  correctness are also outside this slice.
- **No full resource soundness.** Captured/nested borrows, pending receives,
  affine owners, joins, loops, effects, and `satisfies C` still require
  separate work. Do not graduate the FSEM-01 rules as normative.

**Next target:** introduce an exact-versioned, source-derived observation
artifact plus a formally checked decoder/step checker (or an extracted
checker) so the cross-language evidence itself has a proved, inspectable
boundary. That—not another snapshot comparison—is needed before claiming
an implementation simulation result.
