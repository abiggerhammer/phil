# PHIL-DATA-ELIM-001 — consuming elimination and scoped borrow proof

This proof certifies the Phase 1 aggregate-elimination boundary over the already implemented DATA-004–006 behavior, with the later affine-omission pressure case reconciled as DATA-016.

## Certified semantic core

`proof/Phil/Core/DataElimination.v` proves:

- an accepted elimination plan binds every linear field/payload exactly once;
- affine fields/payloads may be bound at most once or omitted;
- duplicate field-disposition entries reject;
- implicit partial aggregate remainders reject; any admitted partial remainder must be explicitly typed;
- consuming a linear aggregate removes the predecessor aggregate owner, by composition with the existing Core `consumeLinear` theorem;
- a bound linear successor is installed in exactly the linear zone and the same successor occurrence cannot be installed twice;
- beginning a restricted aggregate borrow leaves every ownership binding map unchanged and marks exactly the aggregate owner as loaned;
- a live loan prevents linear owner movement and cannot cross the lexical loan boundary;
- ending the loan clears the loan bit while preserving all ownership binding maps; and
- borrowing an undeclared field rejects, while a successful field borrow uses the exact declared field selected by the lookup.

The proof is representation-neutral with respect to nominal record versus sum syntax. Both consuming record destruction and consuming sum matching instantiate the same semantic pattern: consume the aggregate owner, restore only constructor/field-local successors, and manufacture no hidden remainder ownership.

## Correspondence gate

The dedicated `Phase 1 Data Elimination Proofs` workflow compiles the theorem under Rocq 9.2.0, records source and `.vo` identities, typechecks the unchanged implementation paths under `-Wall -Werror`, and reruns the unchanged correspondence corpus:

- `Phase1ConsumingRecordDestructionMain.hs` — 3 cases;
- `Phase1MissingLinearFieldDispositionMain.hs` — 4 cases;
- `Phase1ConsumingSumMatchMain.hs` — 3 cases;
- `Phase1BorrowedAggregateInspectionMain.hs` — integrated DATA-006 borrow assertions;
- `Phase1AffineOmissionMain.hs` — 3 cases.

## Deliberate Phase 1 boundary

The no-partial-move result is a language boundary, not a claim that typed remainders are impossible in principle. Phase 1 has no implicit `record minus field` or `sum minus payload` state. A future partial-move feature must expose an explicit typed remainder operation and prove its ownership semantics separately.

## Residual assumptions / non-claims

This is semantic certification, not implementation refinement. The following remain explicit correspondence or trust boundaries:

- concrete Haskell `Map`/`Set` representation and diagnostic ordering;
- source record/sum declaration elaboration and constructor/tag-to-field correspondence;
- exact correspondence between concrete affine consumption and the normalized affine-disposition theorem;
- lexical-scope elaboration for borrowed views;
- concrete aggregate construction/destruction orchestration;
- Haskell implementation equivalence; and
- Rocq kernel/toolchain correctness.

`PHIL-DATA-MODE-001` supplies the Certified aggregate structural-mode dependency. Core one-shot linear ownership is reused rather than duplicated here.
