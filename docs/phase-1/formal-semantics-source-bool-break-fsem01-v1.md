# FSEM-01 L-1 — source loop break, lexical exit and terminal linear completion

> **Status: bounded, non-normative source/production evidence under review.**
> Tracks [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613),
> [FSEM-01 exit matrix](formal-semantics-fsem01-exit-matrix-v1.md)
> R12/R15 and the already merged
> [continuing-backedge slice](formal-semantics-source-bool-loop-fsem01-v1.md).
> This is not general source loop execution, type soundness or implementation refinement.

## Genuine parsed-source break and return

~~~phil
fn exit(seed : Bool, payload : Bytes[8]) -> Bytes[8] satisfies C {
  loop state (cursor : Bool = seed) invariant cursor == cursor {
    break;
  };
  return payload;
}
~~~

Unlike #1703's unconditional continue, this source has a **zero-actual break**
and an actual post-loop terminal return that must consume the Linear Bytes
owner. The [source bridge](../../src/Phil/Surface/GrammarV1/SourceBoolLoopBreak.hs)
admits a nonrecursive, nongeneric function with checked Bool seed, Linear
Bytes[N] payload, identical result type, and one typed Unrestricted Bool
header. Its negative terminal-debt control admits a third *source-declared*
Linear Bytes owner; there is no invented ghost resource or trusted snapshot.

[LoopStateScope](../../src/Phil/Surface/GrammarV1/LoopStateScope.hs)
resolves the initializer in the pre-header scope, allocates the exact
declaration-rooted header identity, validates invariant references in the
header scope, and identifies the final body break. [LoopControl](../../src/Phil/Surface/Check/LoopControl.hs)
checks its zero exit-actual contract; bare and empty-parenthesized break
both supply zero values. The following return must resolve in the **post-loop
lexical scope** to the original payload key.

## Production state and failure sequence

The opt-in [Engine](../../src/Phil/Surface/Check/Engine.hs) path reuses
normal production operations rather than declaring a successful exit from
syntax alone:

1. Initialize exact source-checked resource context. Check the actual
   initializer with checkValueBlock/pruneScopedPath as Unrestricted Bool.
   A Linear Bytes initializer is TypeMismatch before the header.
2. Use insertBindingMeta/Core.Context.insertBinding for the fresh header.
   Only literal true or exact checked cursor == cursor discharge the
   invariant; false/nonreflexive forms yield MissingEvidence before exit.
3. After the checked zero-actual break, invoke production pruneScopedPath
   to remove the local header from both Surface metadata and native Core
   while retaining every pre-loop Linear owner.
4. Run the source-authorized return payload via ordinary checkStatements,
   moveVariable, returnPath, finalizePath and ensureTerminalState. The
   returned owner is consumed once and real Core ensureComplete must
   accept the remaining resource/loan state.

The independently executed normal and traced checkers must agree. The trace
records exact native before/entry/header/exited/terminal contexts only at
actually reached cuts. No rejected statement fabricates a post-error
terminal state.

## The decisive minimally rejected owner debt witness

~~~phil
fn exit(seed : Bool, payload : Bytes[8], debt : Bytes[4]) -> Bytes[8] satisfies C {
  loop state (cursor : Bool = seed) invariant cursor == cursor {
    break;
  };
  return payload;
}
~~~

Here debt is a genuine independently source-checked Linear parameter, not
an injected model object. The return consumes payload but leaves debt.
The terminal production checker must reject its exact native owner map
as UnconsumedLinearResources, exposed as LinearCompletion; the exit resource
cut exists, but no successful terminal resource cut is invented.

The [19 parsed source fixtures](../../test/fixtures/fsem01-source-bool-break-v1/accepted-reflexive.phil)
and [strict regression driver](../../test/Phase1FSEM01SourceBoolBreakMain.hs)
exercise both accepted invariants, the two zero-actual break spellings,
type mismatch before header, unproved invariant before exit, one/two
break-actual arity failures, source forward reference and active shadowing,
and the precise terminal unpaid-owner error. Unsupported alternative
loop/control/return forms remain adapter noncompetence, not normative
source rejection.

## Rocq model and explicit nonclaims

[SurfaceSourceBoolLoopBreak.v](../../proof/Phil/Surface/SurfaceSourceBoolLoopBreak.v)
reuses [Context.v](../../proof/Phil/Core/Context.v) and
[earlier Bool join lemmas](../../proof/Phil/Surface/SurfaceSourceBoolJoinTelescope.v).
Under the stated successful native-model insert/consume premises it proves:
fresh header removal; preservation of unrelated Unrestricted names, Linear
spectators and loans through scope closure; exact returned Linear owner
consumption; terminal no-debt when no other owner is live; and refusal of
terminal completion if an additional Linear debt survives. No new Axiom,
Admitted or Parameter statements. This conditional model is NOT universal
Haskell↔Rocq state refinement.

FSEM-01 remains **OPEN**. Dynamic loop iterations, arbitrary bodies, nested
loops, nonempty break exit-state telescopes, mixed/linear/affine/dependent
header state, source loan escapes and general invariants are all outside this
bounded slice. FSEM-05's executable reference interpreter, FSEM-06's
implementation correspondence, FSEM-07 normative graduation and assurance
discharge of the source satisfies-C clause remain separate.
