# FSEM-01 L-2 — parsed-source Linear Bytes loop owner transfer

> **Status: bounded and non-normative; proof/test correspondence under review.**
> Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613),
> [FSEM-01 exit matrix](formal-semantics-fsem01-exit-matrix-v1.md)
> R12/R15. Follows merged Bool
> [continue](formal-semantics-source-bool-loop-fsem01-v1.md)
> and [break/terminal](formal-semantics-source-bool-break-fsem01-v1.md)
> slices. Neither dynamic loop execution nor general implementation
> refinement follows from this fragment.

## A genuine Linear source-state transfer

~~~phil
fn cycle(flag : Bool, payload : Bytes[8]) -> Unit satisfies C {
  loop state (owner : Bytes[8] = payload) invariant true {
    continue(owner);
  };
}
~~~

The real Grammar-v1 parser and existing [LoopStateScope](../../src/Phil/Surface/GrammarV1/LoopStateScope.hs)
resolve the initializer in the pre-header scope, then allocate a fresh
declaration-rooted owner state binder and resolve the explicit continue
actual in the loop body. Independently checked source types give the
original payload and header exactly Linear Bytes[N], matching in width.
[LoopControl](../../src/Phil/Surface/Check/LoopControl.hs)
checks one actual, never an implicit capture.

[The source adapter](../../src/Phil/Surface/GrammarV1/SourceLinearLoopTransfer.hs)
admits a nonrecursive, nongeneric one-slot source loop with an Unrestricted
Bool flag, Linear Bytes[N] payload and Unit result. For negative cases an
optional additional *source-declared* Linear Bytes[M] owner is admitted,
rather than injecting a fabricated resource snapshot. Only one statically
checked continuing predecessor is modeled. There is no terminal path,
dynamic iteration or whole-function Linear completion assertion; the
satisfies-C assurance remains unproved.

## Real production resource states

The [Engine extension](../../src/Phil/Surface/Check/Engine.hs) independently
runs ordinary Surface checkValueBlock/pruneScopedPath and
moveVariable/Core.useBinding. Exact source-derived value/type/mode
checking gates both entry and continue.

1. Evaluating the actual entry initializer consumes the old Linear
   payload owner *before* the header exists.
2. The real insertBindingMeta/Core.Context.insertBinding operation installs
   the checked Bytes[N] owner under the fresh header identity. The old
   name is absent; there is no multiplication of Linear owners.
3. The checked invariant literal true permits one static backedge.
   False produces MissingEvidence after header creation and before continue.
4. Evaluating the actual continue(owner) consumes that header owner.
   A second real Core insertBinding operation restores **the same header
   identity** from the consumed successor. This succeeds only if the old
   header was actually consumed.
5. Native joinExclusive/Core.Context.joinContinuing reconciles the
   reconstituted backedge with the header's resource context, requiring
   matching Linear owner names/types and no escaping loans.

An independent tracer reruns the ordinary checker and records only
reached before/entry-consumed/header-bound/backedge-consumed/
backedge-rebound/reentered contexts. A rejected path cannot invent
a later checkpoint. These are *static ownership transitions*, not
an unbounded operational evaluator.

## Actual accepted/rejected source witnesses

[The strict source driver](../../test/Phase1FSEM01LinearLoopTransferMain.hs)
uses [23 parsed fixtures](../../test/fixtures/fsem01-linear-loop-transfer-v1/accepted-owner.phil).
The accepted examples include a one-owner loop, alpha-renamed header,
and an independently source-declared Linear Bytes spectator kept intact.
Every successful native resource Map/Set cut is compared against
independently called Core.consumeLinear, Core.insertBinding and
Core.joinContinuing.

Decisive negative witnesses:
- **Stale original:** continue(payload) after entry consumed payload gives
  StructuralUse at the exact source name, before any backedge/rebind.
- **Wrong type/width:** continue(flag) or continue(alternate) with
  alternate:Bytes[4] in a Bytes[8] header gives TypeMismatch.
- **Duplicate still-live header:** continue(alternate) with another
  alternate:Bytes[8] consumes that other owner but leaves the original
  header live. A real Core DuplicateBinding / Surface StructuralUse
  rejects replacing the header, with no reentry successor.
- **Unproved invariant:** false gives MissingEvidence before a backedge.
- **Arity/scope:** zero or two continue actuals give exact LoopControl
  arity errors; forward initializer and shadowed header fail through
  the existing lexical authority.

Unsupported source forms return adapter noncompetence; this is not a
normative language-invalidity judgment.

## Conditional Rocq model and remaining gaps

[SurfaceSourceLinearLoopTransfer.v](../../proof/Phil/Surface/SurfaceSourceLinearLoopTransfer.v)
composes proven Context.consumeLinear and Context.insertBinding facts with
ContextJoin.context_join_linear_converges and the closed-loan result. It
shows that the old owner is consumed before a fresh header is installed,
the old name remains absent when distinct, the header is consumed/rebound
for a backedge, every Linear lookup agrees on reentry, and a second
insertion over a still-live header is rejected. No new axioms or admissions.

The Core model theorems are conditional, while the finite Haskell checker
tests actual source/native Map/Set behavior. The correspondence is **not**
full Haskell-to-Rocq representation or error refinement.

Still open: multi-slot, dependent and mixed-mode loop state; arbitrary
body statements and multiple backedges; nonempty break-exit state;
scoped-loan escape; dynamic iteration and arbitrary invariants;
source-to-Systems CFG elaboration and universal implementation
correspondence. FSEM-05/06/07 and satisfies-C discharge remain separate;
FSEM-01 stays OPEN.
