# FSEM-01 — lexical shared loans at source branch/join boundaries

> **Status: bounded, non-normative source-to-production evidence.**
> Tracks [issue #1613](https://github.com/abiggerhammer/phil/issues/1613),
> [FSEM-01 rule-family exit matrix](formal-semantics-fsem01-exit-matrix-v1.md)
> R05/R10/R11/R15, and the preceding
> [J-1/J-2 source join](formal-semantics-source-branch-join-fsem01-v1.md)
> and [affine scope](formal-semantics-affine-join-scope-fsem01-v1.md)
> slices. These checks are not whole-language operational semantics,
> source-to-Rocq checker simulation, or proof of the Haskell runtime.

## 1. An actual Grammar-v1 borrow in a source if

The accepted fixture is:

~~~phil
fn choose(flag : Bool, payload : Bytes[8]) -> Bytes[8] satisfies C {
  if flag join state () {
    borrow payload as view { view; unit; };
  } else {
    unit;
  };
  return payload;
}
~~~

The [source bridge](../../src/Phil/Surface/GrammarV1/SourceScopedBorrowJoin.hs)
parses this exact function and checks both parameter types independently:
`flag : Bool` is Unrestricted; `payload : Bytes[8]` is intrinsically
Linear. It rejects unchecked named structural modes and arbitrary source
shapes rather than guessing a type. The existing
[Grammar-v1 source binder authority](../../src/Phil/Surface/GrammarV1/BinderScope.hs)
allocates exact parameter identities and distinct branch-child scopes.
Each source borrow uses the existing
[BorrowViewScope](../../src/Phil/Surface/GrammarV1/BorrowViewScope.hs)
to resolve the source owner **before** allocating its view binder;
[LetPatternScope](../../src/Phil/Surface/GrammarV1/LetPatternScope.hs)
resolves any body aliases against the active borrow view or parameter.
The borrow-view frame and branch frame both close before the next
sibling; neither their local names nor their previous ordinals are
incorrectly reused.

Two branches may spell their views `view` without sharing semantic
Core names. The source condition and post-if return are checked
against their exact original parameter binders, not reconstructed from
display spelling.

The only admitted control shape is one nonrecursive, nongeneric function,
one two-arm source `if flag join state ()` with an empty state telescope,
one Unit or borrow-expression statement per arm, a small lexical
borrow body of resolved local value/unit/let statements, then a return
of the exact source payload. There is no unchecked source if lowering,
dynamic branch execution, full CFG or scheduler in this adapter.

## 2. Actual production loan closure before native join

The source adapter projects only the already-checked binder identities into
the existing [Surface checker](../../src/Phil/Surface/Check/Engine.hs).
Both predecessor blocks start from the same initialized real Core state.
The ordinary checker executes `checkBlock`, which uses its existing
`evalBorrow`/`evalBorrowTraced` implementation:

1. The loan's **source-derived owner identity** is present in the
   native Linear map before borrowing.
2. `startSharedLoan` adds that exact owner to the live-loan set,
   temporarily binds an Unrestricted `SharedBytes` view in the nested
   lexical region, and checks the body. A view copied through a local
   alias retains its borrowed-owner shape.
3. A body whose final value is safe (`unit`) has its temporary local
   view/alias names removed, then uses `endSharedLoan` to close the
   exact loan; the Linear owner remains in its original native zone.
4. Actual `pruneScopedPath` checks the enclosing branch's local-resource
   exit. `joinExclusive` delegates the two continuing predecessor
   contexts to `Core.Context.joinContinuing`. On successful closure both
   are loan-free and have the same exact Linear owner; a subsequent
   `return payload` consumes the owner once.
5. For a body returning `view` (directly or via an alias), the real
   evaluator rejects **BorrowEscape** with
   `shared view escapes its lexical scope`. The branch fails before
   producing a raw predecessor, before scope pruning, before its
   sibling can be evaluated if it is the first arm, and before any join.
   No post-error continuation, loan close or joined state is invented.

The earlier
[production scoped-join observer](../../src/Phil/Surface/Check/Engine.hs)
records the actual branch raw/pruned contexts and joined result, and
runs ordinary checking independently to compare its outcome.
This slice adds a **read-only branch loan observer** that calls the
very same `evalBorrowTraced` procedure from the exact initialized
state, retaining the loan-start/body/close or rejection-prefix
checkpoints. Its negative error outcome is cross-checked against the
ordinary source-branch checker. This observer runs an independent
checker replay; finite equality of observed states is **not** a theorem
that all interpreter paths or runtime representations are equivalent.

At the observed `TraceLoanStarted` cut, native
`Core.joinContinuing [started, initial]` must return the precise
`EscapingLoans` error. At the real successful `TraceLoanClosed` cut,
`Core.joinContinuing [closed, initial]` must succeed with the unchanged
resource context. No source execution is pretended to join the
still-live intermediate loan: that counterfactual is a
separately checked *native Core* rejection control.

## 3. Source specimens and precise negative controls

The strict
[Phase1FSEM01ScopedBorrowJoinMain.hs](../../test/Phase1FSEM01ScopedBorrowJoinMain.hs)
reads 18 real source fixtures in
[test/fixtures/fsem01-scoped-borrow-join-v1](../../test/fixtures/fsem01-scoped-borrow-join-v1/accepted-left.phil).

| Source witness | Expected actual production/source-scope result |
| --- | --- |
| [Accepted left](../../test/fixtures/fsem01-scoped-borrow-join-v1/accepted-left.phil), [accepted right](../../test/fixtures/fsem01-scoped-borrow-join-v1/accepted-right.phil) | Exact source owner/view trace: BeforeLoan → LoanStarted → BodyResult(false) → LoanClosed. Both branches enter the continuing join with identical Γ/A/Δ/loan state; the function returns the same Linear Bytes owner. |
| [Both branches borrow](../../test/fixtures/fsem01-scoped-borrow-join-v1/accepted-both.phil) | Both real source loans close, and two distinct source-rooted semantic view identities are retained in the evidence despite the identical spelling `view`. |
| [Local alias is safely discarded](../../test/fixtures/fsem01-scoped-borrow-join-v1/accepted-alias.phil) | A local unrestricted alias of the borrowed view disappears before the loan closes. The owner and join remain valid. |
| [Escape from first branch](../../test/fixtures/fsem01-scoped-borrow-join-v1/escape-left.phil) | Minimal source mutation deletes the body's final `unit;`, making `view` its result. Exactly BorrowEscape; no LoanClosed, right-arm processing or joined context. |
| [Escape from second branch](../../test/fixtures/fsem01-scoped-borrow-join-v1/escape-right.phil) | The first Unit arm completes. The second source loan yields BorrowEscape, with no fabricated right predecessor or join. |
| [Escape through alias](../../test/fixtures/fsem01-scoped-borrow-join-v1/escape-alias.phil) | Returning the alias still contains the borrowed view; exactly the same BorrowEscape rejection class and fail-closed prefix. |
| [Move owner while loaned](../../test/fixtures/fsem01-scoped-borrow-join-v1/move-while-loaned.phil) | Moving the exact Linear owner from a nested borrow body is prohibited by the existing Core ownership checker; StructuralUse occurs before a completed body/loan-close/join. |
| [Return during loan](../../test/fixtures/fsem01-scoped-borrow-join-v1/return-inside-borrow.phil) | The normal terminal completeness gate rejects the live loan as LinearCompletion, without a joined state. It is a *distinct* diagnostic from a borrow-result escape. |
| [Borrow Unrestricted Bool](../../test/fixtures/fsem01-scoped-borrow-join-v1/borrow-unrestricted.phil) | The real borrow checker reports BorrowEscape with precise non-owner detail before starting any loan. |
| [Shadow parameter with view name](../../test/fixtures/fsem01-scoped-borrow-join-v1/view-shadow-parameter.phil) | Existing source binder authority rejects the active shadow through its exact GrammarV1ActiveShadowing category. |
| Post-join view name, nonempty join state, missing else, wrong result width/condition, unknown source owner, nested borrow | Deliberately outside the bounded adapter. A `Nothing` result does *not* establish normative language invalidity or full source lexical soundness. |

## 4. Conditional Rocq and explicit trust boundaries

[SurfaceSourceScopedBorrowJoin.v](../../proof/Phil/Surface/SurfaceSourceScopedBorrowJoin.v)
reuses the established
[ContextJoin.v](../../proof/Phil/Core/ContextJoin.v) success relation.
The new Rocq theorems prove that:

- a live loan in **either** continuing predecessor contradicts a
  successful modeled join;
- accepted modeled joins have no active loans in either predecessor
  and no active loans in the joined state;
- the bounded modeled rejected-borrow outcome supplies **no**
  continuing predecessor, while successful closure preserves its
  exact context parameter.

The model is compiled by Rocq 9.2 without new axioms or admissions.
It does **not** prove the Haskell lexical traversal, Map/Set/Text,
borrow evaluator, error classification, or the whole source transition
relation. Those concrete facts are enforced only by finite
source-derived tests with exact checker outcomes. Neither the source
`satisfies C` clause nor any external assurance obligation is
discharged here.

## 5. What remains for FSEM-01 exit

This slice reduces the branch/loan gap, but **FSEM-01 stays open**:
nonempty join-state telescopes/invariants, fully general source
branches and loops, mutable/exclusive or nested borrowing,
external captures/closures, resource-typed terminal/failure arms,
general source-to-Core-to-Rocq representation/error preservation,
and the accepted-construct coverage decision remain separate.

Full extracted executable reference semantics is tracked by FSEM-05;
general implementation correspondence by FSEM-06; and normative
adoption by FSEM-07. This note does not change those authority lines.
