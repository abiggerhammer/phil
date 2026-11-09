# FSEM-01 L-1 — parsed-source Bool loop entry and backedge

> Status: bounded, non-normative source/resource correspondence, under review.
> Tracks [issue #1613](https://github.com/abiggerhammer/phil/issues/1613) and
> [the FSEM-01 exit matrix](formal-semantics-fsem01-exit-matrix-v1.md) R12/R15.
> This is not a complete loop evaluator or universal Haskell-to-Rocq refinement.

## Exact parsed-source witness

~~~phil
fn cycle(seed : Bool, alternative : Bool, payload : Bytes[8]) -> Unit satisfies C {
  loop state (cursor : Bool = seed) invariant cursor == cursor {
    continue(alternative);
  };
}
~~~

The body contains an **unconditional continuing backedge**; it is not a
terminating runtime function. The Linear Bytes payload is an unchanged
spectator. There is no terminal path proving that it is eventually consumed.
Only this **one static reentry boundary** is claimed. Accepting the bounded
source bridge does not certify global function well-typedness.

[SourceBoolLoopResource](../../src/Phil/Surface/GrammarV1/SourceBoolLoopResource.hs)
admits one nonrecursive, nongeneric source function with two actual
Unrestricted Bool parameters, a Linear Bytes spectator, and one independently
checked Unrestricted Bool loop-header slot. The entry initializer and
continue actual must be simple lexically resolved source variables. Unsupported
expressions, dependent or multi-slot state and complex loop bodies explicitly
remain out of this adapter's competence.

[LoopStateScope](../../src/Phil/Surface/GrammarV1/LoopStateScope.hs)
owns exact lexical identities and scopes: all initializers are checked
**before header binding**; the header binder is fresh and declaration rooted;
the invariant sees the complete header; and the continue actual is resolved in
the nested loop body. The adapter checks the exact source spans and binder keys
and never reconstructs identity from a display spelling. Existing
[LoopControl](../../src/Phil/Surface/Check/LoopControl.hs) checks the explicit
continue arity: zero actuals do not silently inherit state.

## Actual production resource transitions

The opt-in [Engine](../../src/Phil/Surface/Check/Engine.hs) entrypoint uses
the ordinary Surface and native Core resource checker. It does not
interpret dynamic loop iterations.

1. Initialize the production context from independently checked source
   parameter types/modes and exact declaration-rooted names. Evaluate the
   real entry expression through checkValueBlock / pruneScopedPath, requiring
   one real Unrestricted Bool value. A Linear Bytes initializer fails
   TypeMismatch **before** creating a header.
2. Use insertBindingMeta / native Core.Context.insertBinding to introduce
   exactly the new typed header state slot. The initial linear spectator,
   affine collection and active shared-loan set are preserved.
3. Explicitly justify literal true or exact checked cursor == cursor, and
   reject false/nonreflexive predicates as production MissingEvidence.
   An unproved invariant stops here before a backedge.
4. Evaluate the source continue operand through the same real production
   value and scope checker from the bound header context. A Linear Bytes
   value supplied where Bool is required yields the exact backedge
   TypeMismatch, without a fabricated reentry.
5. Reconcile the actual header and continuing backedge context with
   joinExclusive / Core.Context.joinContinuing, preserving all four
   resource collections. No normal successor is fabricated after an
   unconditional continue.

The independent ordinary checker and tracing execution must agree. The
trace records the exact native Map/Set checkpoint values only where reached:
before, entry, header, backedge, and reentered.

## Parsed accepted and rejected specimens

[The 18 real source fixtures](../../test/fixtures/fsem01-source-bool-loop-v1/accepted-reflexive.phil)
are read by [the strict test driver](../../test/Phase1FSEM01SourceBoolLoopMain.hs).
Accepted tests distinguish entry from seed versus alternative, continue from
an external Bool versus the fresh header, and literal-true/reflexive
invariants. Negative controls isolate:

- wrong entry and backedge modes/types: exact production TypeMismatch,
  with no invented later cut;
- bare zero-actual and explicit two-actual continue: real
  LoopControlArityMismatch before any source reentry;
- forward header initializer and active-name collision: exact
  LoopStateScope reference/binder error before native projection;
- false and nonreflexive invariant: MissingEvidence after header binding
  but before backedge checking.

Unknown actuals, unsupported literal backedges, missing invariants,
non-Bool or multi-slot state are *adapter noncompetence*, not normative
language invalidity.

## Conditional Rocq proof and unproved boundaries

[SurfaceSourceBoolLoopBackedge.v](../../proof/Phil/Surface/SurfaceSourceBoolLoopBackedge.v)
reuses the existing
[ContextJoin](../../proof/Phil/Core/ContextJoin.v) and
[one-slot resource lemmas](../../proof/Phil/Surface/SurfaceSourceBoolJoinTelescope.v).
Conditional on actual checked insertion and ContextJoinSuccess premises,
it proves the fresh exact header, linear-spectator preservation at the header
and initial/backedge reentry, and closed loan state. It separately models
refusal of restricted-mode Bool actuals and unproved invariants.
No new Axiom, Admitted or Parameter declarations are introduced.

This does **not** establish actual loop execution, arbitrary invariant
preservation, zero-loan safety for all source bodies, full Haskell
Map/Set/Text correspondence with Rocq, or universal error-class simulation.

## Remaining FSEM-01 and other tranche obligations

Still open: multi/dependent state, nontrivial affine/linear ownership moves,
nested bodies and loops, scoped-loan escape across backedges, break/exit
control and terminal linear completion, arbitrary invariant obligations,
full source-to-Systems CFG projection and source-wide error preservation.
The separate FSEM-05 extracted executable source semantics, FSEM-06
implementation refinement, and FSEM-07 normative graduation remain open.
The source satisfies-C assurance obligation is not discharged here.
