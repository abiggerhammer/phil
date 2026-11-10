# FSEM-01 CORR-1 C-1 — source capture checkpoints and negative-prefix replay

> **Non-normative bounded source/native/model correspondence; FSEM-01 stays OPEN.**
> Tracks [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613), [COVERAGE-1](formal-semantics-fsem01-coverage1-v1.md) rows CAP-01/CAP-02, and exit-matrix R13/R15. Builds on merged [C-1 #1712](https://github.com/abiggerhammer/phil/pull/1712). No accepted syntax, semantic contract, proof authority, or TCB changes.

## The exact source path

These are two *genuine complete parsed Grammar-v1 functions*, evaluated through the existing bounded C-1 adapter, not generated ownership models.

~~~phil
fn build(flag : Bool, payload : Bytes[8]) -> OneShot satisfies C {
  return closure mode linear () satisfies OneShot captures (flag, payload) { unit; };
}
~~~

~~~phil
fn scope(flag : Bool, payload : Bytes[8]) -> Unit satisfies C {
  borrow payload as view {
    closure mode unrestricted () satisfies OneShot captures (view) { unit; };
    unit;
  };
}
~~~

The first source resolves each capture to a declaration-rooted binder identity, validates the normalized capture summary, then calls the native `Core.useBinding` for every ordered capture. The production [source adapter](../../src/Phil/Surface/GrammarV1/SourceClosureCapture.hs) now retains `directCuts`: the initial actual `Core.ResourceContext` and every *successful* next state returned by the real native call. Repeated `Bool` copies appear as distinct successful cut points with unchanged resource contexts; a `Linear Bytes[8]` move removes exactly its own entry from the native Linear map. Every cut includes the complete unrestricted, affine, linear and shared-loan collections, not a guessed isolated owner boolean.

The independent [CORR-1 replay checker](../../src/Phil/Surface/GrammarV1/SourceClosureCaptureCorrespondence.hs) reconstructs the capture description/mode and normalized `Core.Callable.checkClosureCaptures` summary from the source-derived capture keys and original context, independently replays `Core.useBinding` in source order, and compares the entire cut list, final state, exact outcome and failure stage. It refuses forged snapshots, missing summaries, incorrect stages and invented post-rejection states. This checks a deterministic production observation at an exact bounded source edge, **not** a universal source-to-Haskell refinement theorem.

The second source begins a native `Core.startSharedLoan` on the source-resolved owner and checks the view's precise loan key through `Core.CallableScope.checkClosureCaptureScope`. The adapter now retains `borrowCuts`: initial state, actual loan-open state, then loan-closed state **only** if `Core.endSharedLoan` succeeded. Replacing the local closure expression with a return produces a real `EscapingClosureCapturesScopedLoan` rejection after loan start: that trace stops at `[initial, loaned]` with `borrowClosed = Nothing`. That loan-open prefix is evidence of earlier successful work, *not* an accepted post-failure successor.

## Exact stage boundary

| Source observation | Origin and native evidence | Terminal/continuing state |
| --- | --- | --- |
| Unknown capture or active lexical shadow | `grammarV1ResolveLocal` returns `Just (Left SourceClosureBinderError ...)` before a `SourceDirectClosureRun` exists | No resource run and no fabricated context |
| Duplicate restricted capture | `checkClosureCaptures` fails at `ClosureCaptureValidation`, before native `useBinding` | `directCuts = [initial]`, `directFinal = Nothing` |
| Capture-mode weakening | Derived minimum mode conflicts with explicitly declared mode at `ClosureModeValidation` | `directCuts = [initial]`, no accepted final state |
| Valid direct capture | Independently normalized source captures, ordered native `useBinding` results | Every genuine context cut retained; `directFinal = Just final` |
| Local scoped capture | Exact loan-start and native scope-containment check followed by loan-close | `borrowCuts = [initial, loaned, closed]`, `borrowClosed = Just closed` |
| Escaping borrowed capture | Native `CallableScope` error at `ClosureLoanScope` | Only initial + successful loan-start recorded; no loan-close successor |
| Unjustified stronger scoped-closure mode | Native source structural-mode gate at `ClosureModeValidation` | Exactly initial + loan-open prefix; no loan-close successor |
| Out-of-fragment source, e.g. recursive function or wrong result nominal | The bounded adapter returns `Nothing` | **Noncompetence, not a normative source-invalidity judgment** |

The [strict Haskell driver](../../test/Phase1FSEM01ClosureCaptureCorrMain.hs) replays 16 complete parsed source specimens, including accepted Linear/copy/mixed/repeated Unrestricted inputs, duplicate, mode, lexical and scoped-loan negative cases, plus eight adversarial changes to native state/summary/stage/extent. It also checks exact stale owner refusal after an accepted Linear move. The existing C-1 driver continues to run, so the new bridge cannot quietly regress prior checked behavior.

## Mechanized conditional model and precise exclusions

[SurfaceSourceClosureCaptureCorr1.v](../../proof/Phil/Surface/SurfaceSourceClosureCaptureCorr1.v) composes existing Rocq `Context`, `CallableMode` and `CallableScope` facts: conditional exact Linear owner removal and spectator frame, no accepted context for failed native consumption, duplicate Linear precheck refusal before a move, active-loan owner refusal, stale-reuse rejection, exact-scope acceptance and escaped scoped-loan denial. All theorems are compiled by Rocq 9.2 without `Axiom`, `Admitted` or `Parameter` in the new file. These are **model-level theorems with explicit premises**, not claims of automatic proof over the Haskell `Map`/`Set` implementation.

The source C-1 adapter recognizes only two function-parameter types (`Unrestricted Bool` and `Linear Bytes[N]`), a narrow complete closure body, and one source-scoped view. Nominal callable `OneShot` result typing, `satisfies C` discharge, source-derived recursive closure graph construction, general closure body and mode checking, nested loans, invocation/authority/effects, compilation and runtime evaluation all remain **outside this CORR-1 slice**. FSEM-04 owns callable effects/authority/assurance; FSEM-05 owns independent executable source semantics; FSEM-06 owns general implementation/elaboration refinement; FSEM-07 owns normative graduation. Neither this bounded bridge nor the 46-entry COVERAGE-1 inventory closes FSEM-01.

## Reproduction

The focused preflight `.github/workflows/fsem01-corr1-closure-capture-preflight.yml` uses GHC 9.6.7 with a warning-free `cabal build lib:phil-core --ghc-options=-Werror`, runs both the existing C-1 and new CORR-1 source tests under `-Wall -Werror`, and compiles the original conditional C-1 model plus the CORR-1 model in Rocq 9.2. Preserve the exact source/head SHA, proof assumptions, tested witness files and any negative test classifications when reviewing the PR.
