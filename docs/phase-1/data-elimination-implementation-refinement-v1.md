# PHIL-DATA-ELIM-001 — implementation refinement staging

This slice extracts bounded executable decisions from the semantics already Certified by `proof/Phil/Core/DataElimination.v`. Production Haskell remains unchanged.

## Exact decision surface

The staged `DataEliminationKernel` owns five representation-neutral decision surfaces:

1. field disposition legality by structural mode: every linear field must be explicitly bound, while affine and unrestricted fields may be omitted;
2. whole-plan admission from two independently established facts: all concrete field dispositions are legal and concrete disposition entries are distinct;
3. aggregate remainder admission: whole consumption and an explicit typed-remainder kind are admissible, while an implicit partial remainder is not;
4. consuming-elimination admission from actual postconditions: the aggregate owner was consumed, restored successors are exact, and successor identities are distinct; and
5. scoped-borrow admission from actual postconditions: the selected field is declared, the real shared loan started, the owner is immobilized while live, an active loan is rejected at the lexical boundary, and ending the loan preserves the owner.

`decideFieldDispositionByMode` is proved equivalent to the Certified `FieldDispositionAllowed` relation for every `DataField`. `decideAggregateDispositionKind` is proved equivalent to `AggregateDispositionAccepted` after erasing only the concrete explicit remainder type. The plan, consuming-transfer, and borrow gates are proved exact for their Boolean facts and have reflection theorems allowing those facts to be instantiated by the Certified semantic predicates.

## Concrete/native boundaries

The kernel does **not** replace Phil's concrete resource machinery:

- `Phil.Core.DataDestruction` continues to own concrete field names, `Map` construction, duplicate-name and unknown-field diagnostic ordering;
- record/sum declaration elaboration, constructor/tag selection, and field ordering remain native;
- actual aggregate consumption and successor restoration remain ordinary `Phil.Core.Context.useBinding` / `insertBinding` operations;
- concrete successor names and freshness remain native; the kernel only receives the resulting exact/distinct facts;
- `Phil.Core.DataBorrow` continues to perform exact field lookup and the actual `startSharedLoan` / `endSharedLoan` calls;
- lexical scope elaboration remains native; the kernel receives only the facts established by the real live-loan boundary checks;
- concrete affine consumption remains native; and
- diagnostic payloads remain native.

A later production-binding closeout may derive kernel Booleans only from those actual checks. Kernel disagreement may only reject. It may not manufacture a field, successor, remainder, loan, or owner state.

## Staging controls

The staging workflow freshly compiles `DataElimination.v` and `DataEliminationImplementation.v` under Rocq 9.2.0, extracts `DataEliminationKernel.hs`, records proof/kernel identities, strict-typechecks and executes 23 direct extracted-kernel controls, then reruns the unchanged DATA elimination/borrow correspondence corpus:

- `test/Phase1ConsumingRecordDestructionMain.hs`
- `test/Phase1MissingLinearFieldDispositionMain.hs`
- `test/Phase1ConsumingSumMatchMain.hs`
- `test/Phase1BorrowedAggregateInspectionMain.hs`
- `test/Phase1AffineOmissionMain.hs`

A green staging merge leaves `PHIL-DATA-ELIM-001` at `Discharged / Certified`. Only a separate exact-kernel production binding may promote it to `Discharged / Implementation Refined`.
