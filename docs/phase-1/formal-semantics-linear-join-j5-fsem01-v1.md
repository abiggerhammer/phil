# FSEM-01 J-5 — source-checked Linear Bytes[N] join-state slot

> **Non-normative bounded resource typing slice.** Follows protected [CORR-7 #1822](https://github.com/abiggerhammer/phil/pull/1822) under [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613). This does not change the normative Grammar-v1 language, grant new trusted premises, implement dynamic phi evaluation, or prove universal Source→Core correspondence.

## Scope: exactly one restricted join-state slot

The existing J-1/J-2 and Bool telescope paths type-check source `if` joins with continuing/terminal predecessor classification and one/two **Unrestricted Bool** slots. J-5 opts into one **Linear Bytes[N]** slot, rather than quietly broadening the generic source checker.

A representative genuine Grammar-v1 declaration is:

```phil
fn choose(flag : Bool, payload : Bytes[8]) -> Bytes[8] satisfies C {
  if flag join state (selected : Bytes[8]) invariant true {
    payload;
  } else {
    payload;
  };
  return selected;
}
```

This is an independently source-scoped two-arm `if`, not proof of arbitrary match, nested control, dependent state, or runtime execution. Both alternatives are *statically checked* and the original Linear owner is consumed exactly once **on each path**. The resulting resource contexts agree with the original owner absent; `joinExclusive` uses the real native `Core.joinContinuing`; a fresh Linear slot is inserted only after the successful join. Returning that new slot performs an actual one-shot Linear move and final terminal completion. No branch invents a new runtime byte value or claims the static join selected a dynamic alternative.

### Actual native authority and source bindings

- [SourceLinearJoinTelescope](../../src/Phil/Surface/GrammarV1/SourceLinearJoinTelescope.hs) parses the unchanged admitted Grammar-v1 source, verifies exact source-rooted parameter, predecessor and post-join binder scopes, checks the declared `Bytes[N]`/Linear mode using the real checked type path, and admits only one narrow two-continuing-predecessor shape.
- [Surface Check Engine](../../src/Phil/Surface/Check/Engine.hs) uses its existing `checkValueBlock`/scoped pruning, `moveVariable`/Core consume, `joinExclusive`, `insertBindingMeta`, explicit `checkBoolJoinInvariant`, real `checkStatements` and `finalizePath`. New bounded entry points `checkSurfaceSourceLinearJoinComponent` and `traceSurfaceSourceLinearJoinComponent` share those same primitives and compare independent ordinary vs traced outcomes. A failed predecessor or invariant does **not** produce a fabricated post-error successor.
- [Strict source test](../../test/Phase1FSEM01LinearJoinTelescopeMain.hs) checks 14 real parsed sources in [fixtures](../../test/fixtures/fsem01-linear-join-telescope-v1/), exact declaration-rooted source names, full four-zone before/after context, both checked Linear operand types, new slot freshness and one-shot consumption, precise rejection class and causal error detail. It independently replays genuine native `Core.consumeLinear`/ `joinContinuing` / `insertBinding` and refuses a live loan or unequal Linear predecessor.

### Paired accepted and precise negative evidence

- `accepted-true` and `accepted-reflexive` require respectively a literal true or the same checked slot binder's reflexive invariant. Arbitrary source `satisfies C` obligations are **not** discharged here.
- `unproved-false` produces `MissingEvidence` only after reaching both source value/checker predecessors and binding the new slot; false is not treated as true.
- `wrong-then-bool`, `wrong-else-bool`, and `wrong-slot-width` produce precise `TypeMismatch` at the relevant predecessor, before any joined/bound successor.
- `stale-return` retains the real joined/bound cut but then rejects use of the spent original source Linear owner as `StructuralUse`, with no invented successful return.
- `shadow-parameter` rejects duplicate join binder at lexical scope authority. Six additional parseable out-of-fragment specimens (including forward join-slot reference, absent invariant/else, two slots, wrong result width and wrong condition) are explicitly **adapter noncompetence**, not a claim that their general Phil syntax is invalid.
- Independent native Core adversaries refuse a borrowed original owner as `OwnerBorrowed`, a live loan at join as `EscapingLoans`, unequal Linear maps, duplicate active slot insertion and stale original-owner consumption.

## Conditional Rocq theorem boundary

[SurfaceSourceLinearJoinTelescope.v](../../proof/Phil/Surface/SurfaceSourceLinearJoinTelescope.v) reuses the actual non-normative `Context` and `ContextJoin` models to prove, under explicit legitimate consume/join/insert hypotheses: both statically checked predecessor moves spend the source owner; the merged resource state cannot resurrect it; the slot is fresh and Linear; unrelated Linear spectators are preserved; successful join has no active loans; duplicate slot insertion refuses; terminal return consumes that slot once; and a borrowed owner cannot be moved. These are genuine kernel-checked Core-model theorems, **not** a proof of universal Haskell `Map`/`Set`/`Text` implementation fidelity or of source→machine-code correctness.

A byte value returned by this bounded static checker is typed as `Bytes[N]`, but no dynamic phi behavior, byte-content equality between paths, selected runtime owner identity, source executable interpreter, or implementation-wide `satisfies C` theorem is established. External production/assurance source validity and selected P8/P9/P10 authority remain independent.

## Verification and exit

The [dedicated preflight](../../.github/workflows/fsem01-j5-linear-join-preflight.yml) must compile the full Rocq Core dependency and the new proof with Rocq 9.2 (including named `Print Assumptions`, `rocq check` and no `Admitted`/new axiom), and build strict GHC 9.6.7 `-Wall -Werror` native source checker, new 14-source positive/negative driver and predecessor Bool telescope / Linear loop regression tests. Hash source files and checked fixture bytes.

Require complete nontruncated exact-head PR CI, the original unique `fsem-01` pre-PR claim, an independently fresh two-job **post-ready** claim guard, protected squash with the exact head, then trusted exact claim release. Do not mark FSEM-01 or the general JOIN-05 coverage row complete: multiple Linear/Affine slots, dependent state, match joins, nested loans, full Source→Core/Systems and runtime phi remain open. No FSEM-02, P8, P9, P10, FSEM-05/06/07 or Phase 1 freeze authority is granted.
