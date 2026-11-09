# FSEM-01 L-3 — source-scoped loan before a Linear loop backedge

> **Status: bounded non-normative candidate; exact-head CI pending review.**
> Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613),
> [exit matrix R12/R15](formal-semantics-fsem01-exit-matrix-v1.md).
> Follows protected Linear ownership transfer #1708, without general loop
> operational semantics or an implementation-refinement theorem.

## Admitted parsed-source path

~~~phil
fn cycle(flag : Bool, payload : Bytes[8]) -> Unit satisfies C {
  loop state (owner : Bytes[8] = payload) invariant true {
    borrow owner as view { view; unit; };
    continue(owner);
  };
}
~~~

The genuine [Grammar-v1 LoopStateScope](../../src/Phil/Surface/GrammarV1/LoopStateScope.hs)
now delegates a borrow body step to the existing
[BorrowViewScope](../../src/Phil/Surface/GrammarV1/BorrowViewScope.hs).
The original owner is lexically resolved before the view exists; the
view and local body are discarded before the terminal continue is
resolved. Its semantic identity is source-derived, never forged from
a surface string or chosen by the adapter. A reference to that view
at continue is not silently captured; the bounded adapter refuses it.
Unknown out-of-fragment source is noncompetence, not normative
source-invalidity.

The [Linear loop source adapter](../../src/Phil/Surface/GrammarV1/SourceLinearLoopTransfer.hs)
accepts one optional scoped borrow expression before exactly one
continue in a single-state Linear `Bytes[N]` loop with a checked literal
true invariant. Its borrow-body projection admits Unit and exact lexical
value occurrences only; no arbitrary nested statements or bodies.
No other dynamic iteration, multi-slot loop, or `satisfies C` proof is
claimed.

## Real production resource effects

The [Surface checker](../../src/Phil/Surface/Check/Engine.hs) moves the
original Linear owner to a fresh header by its actual value expression;
after invariant checking it runs the ordinary `checkBlock` and
`evalBorrowTraced` scoped resource path, which calls real
`Core.startSharedLoan` and `Core.endSharedLoan`.
Only a successful source-body loan close produces an after-loan state,
and the explicit continue then consumes and rebinds the original
header identity through `Core.useBinding` and `insertBinding`.
`joinExclusive/Core.joinContinuing` checks the complete four native
resource collections. The tracer independently reruns the ordinary
checker, with exact reached start/body/closed loan checkpoints and no
fabricated close/reentry on rejection.

The [strict source tests](../../test/Phase1FSEM01ScopedLinearLoopLoanMain.hs)
read 11 real parsed source witnesses. Accepted lexical alpha-renaming,
borrow-body use and closed loan preserve the exact native flag/owner
maps, their active-loan sets, old owner consumption and post-join header.
The negative witnesses exercise leaked view values (`BorrowEscape`),
attempted move while the loan is live (native `OwnerBorrowed`, surfaced as
`StructuralUse`), stale original owner (`StructuralUse`),
unrestricted borrow source (`BorrowEscape`), wrong continuing actual
(`TypeMismatch`), unproved invariant (`MissingEvidence`) and
unsupported unscoped view/multiple borrow bodies. Independent Core
`consumeLinear`, `startSharedLoan`, `endSharedLoan` and
`joinContinuing` controls reject a live-loan owner move or join.

## Conditional Rocq boundary

[SurfaceSourceScopedLinearLoopLoan.v](../../proof/Phil/Surface/SurfaceSourceScopedLinearLoopLoan.v)
proves a normalized open/close lookup lifecycle, frame-map preservation,
`consumeLinear` refusal under an active loan, the loan-free
precondition of successful Linear consumption, active-loan impossibility
in a successful native-style join relation, and the exact rebound
header/closed-loan conclusion of that relation. It composes existing
Core Context and ContextJoin lemmas. The model does not claim extraction,
source parser fidelity, arbitrary Haskell Map/Set representation or
universal resource/effect-error refinement.

**Still open:** loans intentionally extending across a backedge (they
must be assigned an explicit scope semantics), nested loan/body
control-flow, multi-owner state and dependent slots, nonempty break
telescope, runtime loop execution, FSEM-05/06/07 and FSEM-01 closure.
