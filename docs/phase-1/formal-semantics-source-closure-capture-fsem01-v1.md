# FSEM-01 C-1 — parsed closure capture ownership and bounded scoped-loan validity

> Status: bounded non-normative C-1 **merged in [#1712](https://github.com/abiggerhammer/phil/pull/1712)**, protected squash `28f84201b5007bc89b2e2f48def7f250c75bee8f`; FSEM-01 remains OPEN. Tracks
> [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613),
> exit matrix R13/R15, and callable-scope CALL-010/CALL-014.
> Authority, effects and assurance still belong to FSEM-04.

## Genuine Grammar-v1 source fragments

The first opt-in source path is an explicit closure capture in a returned
closure expression, not a fabricated list of callable resources:

~~~phil
fn build(flag : Bool, payload : Bytes[8]) -> OneShot satisfies C {
  return closure mode linear () satisfies OneShot
    captures (flag, payload) { unit; };
}
~~~

The real Grammar-v1 parser retains the ordered capture names. The
[source adapter](../../src/Phil/Surface/GrammarV1/SourceClosureCapture.hs)
checks independently source-declared Bool (Unrestricted) and Bytes[N]
(Linear) parameter types/modes. Existing
[BinderScope](../../src/Phil/Surface/GrammarV1/BinderScope.hs) resolves each
source capture into its declaration-rooted Core Name (not a spelling-derived
ownership identity), and checks the nested closure parameter scope. Existing
Core.Callable.checkClosureCaptures normalizes duplicate Unrestricted captures,
rejects duplicate restricted captures, and derives the minimum structural mode.
For this narrow adapter, explicitly selected mode must equal the minimum;
strengthening through independently justified callable contracts is outside
its competence. It then calls Core.Context.useBinding on the exact existing
Core resource context, consuming Linear owners, leaving Unrestricted copies,
and recording the four native map/set collections and rejection outcome.

**Authority limit:** this certifies *capture ownership on a parsed source
fragment*, not full source acceptance. The nominal OneShot return type and
satisfies-C declarations are opaque here; no callable contract revision,
invocation/effects, final return typing, target closure conversion, or compiler
refinement is inferred from the spelling.

The second admitted source shape checks a closure contained inside a genuine
parsed borrow region:

~~~phil
fn scope(flag : Bool, payload : Bytes[8]) -> Unit satisfies C {
  borrow payload as view {
    closure mode unrestricted () satisfies OneShot captures (view) { unit; };
    unit;
  };
}
~~~

The lexical view is created with BinderScope's real borrow-view binder kind;
the source capture must resolve to that same semantic binder. Native
Core.startSharedLoan starts the loan on the existing Linear payload, and
Core.CallableScope.checkClosureCaptureScope checks the exact derived validity
key. A local source expression may capture the view and closes through
Core.endSharedLoan. Substituting a source return of the closure for the
local expression yields the existing exact escaping scoped-loan error;
no loan-close successor is fabricated for that error. This is bounded to
one view, one closure, and a Unit body, not general lifetime inference.

## Source and model evidence

The [source driver](../../test/Phase1FSEM01SourceClosureCaptureMain.hs) uses
17 complete parsed source specimens: successful Linear, mixed and
Unrestricted capture lists, repeated Unrestricted capture, omitted explicit
mode and alpha-renamed parameters; minimally rejected repeated Linear,
weakened mode, unbound capture and active shadow; explicit adapter
noncompetence on mismatched opaque result or recursive source; local/escaped
borrowed view, a derived local mode, stronger unsupported view mode, and
wrong captured view. Native Core.consumeLinear/useUnrestricted/loan tests
independently verify exact old-owner removal, no duplication, all four
collections and correct error prefixes.

The existing Core.CallableScope.checkRestrictedRecursiveClosureCycles is
also replayed with a source-derived restricted capture occurrence in an
**explicitly model-supplied** self-cycle. This tests the native graph
check, **not** the source derivation of a closure-environment cycle.
Named recursive callables must not be rejected solely for recursion.

The [conditional Rocq theorem file](../../proof/Phil/Surface/SurfaceSourceClosureCapture.v)
composes existing CallableMode, CallableScope and Context facts: moved
Linear captures and duplicate rejection, exact consume/frame of a source
owner model, refusal to move a loaned owner, exact local-scope acceptance,
escaping scope refusal, and restricted-cycle rejection conditional on
an independently provided graph. No new axioms or admitted proofs.

**Still open:** full closure source/body elaboration, general capture
discovery, nested/multiple borrow scopes, affine/named-mode authority,
restricted capture provenance in a realized closure environment,
source-derived recursive closure graphs, invocation/effects/authority,
satisfies-C discharge, target representation, general Source↔Rocq
simulation and FSEM-05/06/07 graduation. FSEM-01 remains OPEN.

## Merged C-1 evidence and COVERAGE-1 handoff

The unchanged #1712 source head `70fc60ee2bb44ebc60dcb053747735a5c671d927` passed 217 successful exact-head checks plus one intentional skip and a fresh successful post-ready claim guard. Protected squash merge and trusted claim release were independently verified. This is *bounded* source capture ownership/scope evidence, not general callable source acceptance or `satisfies C` discharge. The [COVERAGE-1 inventory](formal-semantics-fsem01-coverage1-v1.md) explicitly tracks source-derived recursive capture graphs, arbitrary closure bodies/nominal contracts, nested loan scopes, and FSEM-04 effects/assurance premises without calling noncompetent source forms invalid.
