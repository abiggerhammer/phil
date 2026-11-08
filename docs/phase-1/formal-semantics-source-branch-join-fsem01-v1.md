# FSEM-01 J-1/J-2 — two source predecessors, exact join and terminal exclusion

> **Status: proposed bounded, non-normative source-to-production evidence.**
> Tracks [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613)
> and [the FSEM-01 exit matrix](formal-semantics-fsem01-exit-matrix-v1.md)
> at rows R10/R11. This is not universal source if/CFG semantics or
> an independently extracted FSEM-05 interpreter.

## The deliberately small source fragment

Positive real Grammar-v1 source (parsed, with exact function/binder identity):

~~~phil
fn choose(flag : Bool, payload : Bytes[8]) -> Bytes[8] satisfies C {
  if flag join state () {
    unit;
  } else {
    unit;
  };
  return payload;
}
~~~

A minimally changed negative replaces **only the first predecessor's
unit statement** with a resource transfer:

~~~diff
  if flag join state () {
-   unit;
+   let saved = payload;
  } else {
    unit;
  };
~~~

This is **not** a dynamic Boolean branch chosen by the evaluator. The
type checker must admit both continuing alternatives, so both are
conservatively evaluated from the same exact initial resource context.
The negative fails at the *real production join*: the first branch
contains a fresh semantic linear owner named saved, while the second
still has payload. A successful join cannot silently drop either
owner merely because one branch is not taken at runtime.

The bounded adapter requires a nonrecursive, nongeneric function with
two source-checked parameters, Bool and intrinsic Linear Bytes[N];
one if-expression with explicit empty join-state and present else;
one simple statement per branch (Unit, moving Bytes to a fresh
single-name let, or terminal return of Bytes); and a post-if return
of the original source linear parameter. Joined type-state
telescopes, invariants, richer branch expressions, named nominal
modes and arbitrary source CFGs remain outside competence. An
adapter refusal is **not** a normative source-invalidity result.
The annotation satisfies C is not discharged here.

## Actual source identity and production join

[SourceIfJoinResource.hs](../../src/Phil/Surface/GrammarV1/SourceIfJoinResource.hs)
uses the real Grammar-v1 parser and
[JoinStateScope](../../src/Phil/Surface/GrammarV1/JoinStateScope.hs)
to resolve the Bool scrutinee, predecessor bodies, new let binders
and post-join result against the same declaration-rooted lexical
scope. Each new predecessor binder has a fresh Core Name, even if
sibling branches reuse the display spelling saved.

The bounded
[Surface checker entry](../../src/Phil/Surface/Check/Engine.hs)
checks both projected branch blocks starting from **one actual
initializeState**. It calls the production checkBlock, checkStatement
and joinExclusive functions, which delegate to native
[Core.Context.joinContinuing](../../src/Phil/Core/Context.hs).
No test-only reconstruction of the joined context is accepted.
A deliberate trace API records the exact native before/then/else
contexts and the joined context only when the production join
succeeds; the ordinary result is required to agree with the traced
result.

This checker entrypoint is **bounded, opt-in and distinct from**
checkSurfaceComponent's ordinary component-body parser: that
legacy carrier does not have an if-expression constructor. This
is not a generic source if elaborator or an assertion that the
whole Phase 1 source compiler routes all ifs through this adapter.

## J-1: continuing predecessor compatibility

At join, the native checker requires matching Unrestricted and
Linear maps from all continuing predecessors, no escaping loans
and the proper intersection of Affine bindings. The positive
fragment records two identical continuing contexts containing
one Unrestricted flag and one Linear payload. The negative
fragment records the distinct post-branch linear maps and
returns **IncompatibleBranchResidue** with the exact native
LinearBranchMismatch detail, without fabricating a joined
successor. Both predecessor contexts remain independently
observable.

The extra negative with let saved = payload in both sibling
branches checks that their two saved names have different
declaration-rooted semantic ordinals, so matching display
spelling cannot fool the linear-join check.

## J-2: terminal paths do not supply continuing context

A separate real source witness has a terminal arm:

~~~phil
fn choose(flag : Bool, payload : Bytes[8]) -> Bytes[8] satisfies C {
  if flag join state () {
    return payload;
  } else {
    unit;
  };
  return payload;
}
~~~

The terminal predecessor consumes payload and has no linear
binding left. It is **excluded from the ordinary continuing
join**, so the surviving else predecessor retains the live
payload and returns it exactly once. Both terminal paths produce
typed Return outcomes; there is no requirement to reconcile
their differing linear maps at an ordinary continuing join.

A second witness makes the else predecessor transfer payload
to saved; the post-if return of stale payload rejects with
StructuralUse, rather than restoring an owner from the
terminal arm. Two terminal arms followed by an additional
return reject ControlAfterTerminal, with no invented continuing
successor. These cases are intentionally separate from
the invalid two-continuing-predecessor J-1 mismatch.

## Native tests and independently checked Rocq model

[The strict source test](../../test/Phase1FSEM01SourceBranchJoinMain.hs)
parses [11 source fixtures](../../test/fixtures/fsem01-source-branch-join-v1/accepted.phil)
and asserts exact Core Map/Set contexts, semantic names, all
predecessor and terminal counts, native joinContinuing results,
and precise production error class plus exact detail. It also
tests missing else, incompatible condition and result types,
an undeclared join slot and unsupported branch syntax without
reclassifying them as normative language errors.

The independent conditional
[SurfaceSourceIfJoinBridge.v](../../proof/Phil/Surface/SurfaceSourceIfJoinBridge.v)
composes [ContextJoin.v](../../proof/Phil/Core/ContextJoin.v)
without new axioms/admissions. It models two continuing
predecessors, excludes a terminal predecessor from the
context list, proves that a linear owner present in only one
predecessor prevents the normalized ContextJoinSuccess
relation, that the lone continuing predecessor retains
its linear lookups, and that successful joins have no
active loans. These are Rocq model statements, not a proof
of the runtime source-predicate/Map/Error equivalence.

## Remaining J-1/J-2 and FSEM-01 obligations

The specific source projection and finite conformance do **not**
complete full FSEM-01. Still open: explicit nonempty join-state
telescope, source-level affine asymmetric join and branch-local
cleanup, checked loan-region scope exit, nested if/match/decide,
all resource-carrying terminal/failure branches and diagnostic
precedence, a general program-to-Core transition relation
including Unicode/Text/Map/Set and native errors, and
FSEM-01's broader loop/capture/aggregate-competence exit matrix.
General FSEM-05 executable source semantics and FSEM-06
compiler correspondence are explicitly separate tranches.

This should be reviewed as **one bounded source join evidence
slice**, not a declaration that all Phase 1 branch resources are
proved safe from the source language.
