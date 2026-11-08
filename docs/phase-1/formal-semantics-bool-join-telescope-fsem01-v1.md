# FSEM-01 — source-checked nonempty Bool join-state telescope and invariants

> **Status: bounded, non-normative source-to-production evidence.** This is
> a follow-up to [the FSEM-01 rule-family matrix](formal-semantics-fsem01-exit-matrix-v1.md)
> R10/R11/R15, the [two-predecessor join](formal-semantics-source-branch-join-fsem01-v1.md),
> [affine scope](formal-semantics-affine-join-scope-fsem01-v1.md), and
> [shared loan closure](formal-semantics-scoped-borrow-join-fsem01-v1.md) slices.
> Tracked by [issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
> This is not a whole-language if/match/loop semantics nor a general invariant solver.

## 1. Real source syntax: one post-join Bool state slot

The accepted source fixture is:

~~~phil
fn choose(flag : Bool, alternative : Bool, payload : Bytes[8]) -> Bytes[8] satisfies C {
  if flag join state (selected : Bool) invariant selected == selected {
    flag;
  } else {
    alternative;
  };
  selected;
  return payload;
}
~~~

This fragment handles **exactly one** nonempty join-state slot, of
intrinsically **Unrestricted Bool** type. The checked lexical
[JoinStateScope](../../src/Phil/Surface/GrammarV1/JoinStateScope.hs)
runs before resource projection and gives the source slot a fresh
declaration-rooted Core binder identity *only after* both predecessor
branch scopes close. The post-join occurrence of `selected` resolves
to this new exact slot key, and the final `return payload` resolves to
the original Linear Bytes binder. No branch is permitted to read
`selected` before its join-state declaration exists.

The type of the slot is checked independently through
[CheckedType](../../src/Phil/Surface/GrammarV1/CheckedType.hs).
Every predecessor's final source variable occurrence is first
resolved by existing `LetPatternScope` to an original checked parameter;
it is then projected to a normal Surface expression. The accepted
example uses **different** source parameters in the then and else
predecessors. They need not represent equal Boolean values at runtime:
a join slot is a typed source-level phi, *not* a proof that the two
predecessors returned the same value.

The bounded adapter
[SourceBoolJoinTelescope.hs](../../src/Phil/Surface/GrammarV1/SourceBoolJoinTelescope.hs)
refuses generic/recursive functions, missing else arms, multi-slot
telescopes, dependent slot types, nested branch expressions, and
unresolved source types/identities. Noncompetence (returning `Nothing`)
does not establish normative source invalidity.

## 2. Production transition and exact resource states

The new opt-in
[production Surface checker entry](../../src/Phil/Surface/Check/Engine.hs)
checks **both** possible source branches statically from the same
actual initialized Core resource context. For each source predecessor:

1. Call existing `checkValueBlock` to evaluate the complete
   source-derived predecessor block **with its final expression
   value preserved**, rather than simply discarding it.
2. Run real `pruneScopedPath` against the exact incoming names; branch-local
   resource debt, value escape or illegal loan state is not ignored.
3. Require precisely one continuing Unrestricted scalar whose actual
   type is Bool. The mode check uses
   `decisionCarrierMode`, so a restricted semantic carrier cannot
   masquerade as a free Boolean merely through its wrapper.
4. Call real `joinExclusive` → `Core.Context.joinContinuing` for the
   two validated predecessor resource states. Unrestricted/Linear
   maps must agree, Affine resources intersect, and active loans
   prohibit a successful ordinary join.
5. **Only after** a successful join, call existing
   `insertBindingMeta`/`Core.Context.insertBinding` with the exact
   source-generated join binder key and checked Unrestricted Bool
   type. Freshness, no owner collision and resource-map preservation
   belong to the existing production binder authority.
6. Check the admitted invariant evidence before running the
   source-derived successor statements. Finally read the new slot
   with normal production `VariableExpression`/`moveVariable` and
   return the preserved Linear payload exactly once.

The independently evaluated ordinary and tracing paths must agree.
The trace records exact native states before either branch,
after each checked predecessor, after the native Core join and after
the post-join binding. It also records actual types/modes of both
predecessor values. A rejection produces **no made-up joined or
post-telescope successor**.

This is a **static** type/ownership bridge. It does not execute a
runtime conditional, materialize a dynamic Bool phi value, define
the complete source operational semantics, or claim executable
FSEM-05 semantics.

## 3. Proof obligations are not optional assumptions

The bounded invariant path is deliberately strict:

| Source invariant | What is proved / checked |
| --- | --- |
| `invariant true` | The parsed literal-true proposition has an immediate, checked trivial discharge. |
| `invariant selected == selected` | Both sides must resolve to **the same exact freshly checked post-join binder**. Equality reflexivity discharges this narrow proposition for any Boolean selected at runtime. |
| `invariant false` | **MissingEvidence**: there is no proof; the production checker rejects after the actual join and slot insertion but before successor statements. |
| `invariant selected == alternative` | **MissingEvidence**: both occurrences may be well scoped, but their equality does not follow from per-predecessor Bool typing. No arbitrary assumption enters the checker. |
| Other relations, absent invariant, dependent/multiple slots | Out of the adapter's explicit competence; no general proof authority is claimed. |

An invariant's checked source lexical references are preserved via
`GrammarV1CheckedJoinClause`. The adapter classifies only source
forms it can substantiate; native checker
`checkBoolJoinInvariant` fails closed for unproved cases. Neither
`satisfies C` nor any arbitrary logical proposition is discharged
by the fact that source syntax parses.

## 4. Exact source conformance and conditional Rocq

The strict
[Phase1FSEM01BoolJoinTelescopeMain.hs](../../test/Phase1FSEM01BoolJoinTelescopeMain.hs)
reads [19 parsed-source fixtures](../../test/fixtures/fsem01-bool-join-telescope-v1/accepted-reflexive.phil).
It compares the actual four-zone native Core state at each cut, checks
exact source binder identities, proves the native slot was fresh via
an independent `Core.insertBinding` invocation, and asserts exact
source checker results and diagnostics. Important negative controls
include:

- [Wrong first predecessor type](../../test/fixtures/fsem01-bool-join-telescope-v1/wrong-then-type.phil):
  one mutation changes `flag;` to `payload;`, returning a Linear
  Bytes owner where a Bool join-state operand is required. Exact
  production `TypeMismatch` occurs before evaluating the else
  predecessor; there is no join or state binder.
- [Wrong second predecessor type](../../test/fixtures/fsem01-bool-join-telescope-v1/wrong-else-type.phil):
  the first source Bool predecessor is preserved, but no joined
  post-state is invented from the ill-typed second value.
- [Unproved invariant](../../test/fixtures/fsem01-bool-join-telescope-v1/unproved-nonreflexive.phil):
  both typed predecessors and the fresh slot exist, but
  `MissingEvidence` stops the successor.
- [Join slot shadows a parameter](../../test/fixtures/fsem01-bool-join-telescope-v1/shadow-parameter.phil):
  the existing source lexical authority rejects the colliding
  post-join binder; no fallback from display spelling is accepted.
- Forward slot use in a predecessor, missing branch, wrong
  result/slot type, missing/unsupported invariant and post-join
  wrong-name use remain excluded from this bounded fragment.

[SurfaceSourceBoolJoinTelescope.v](../../proof/Phil/Surface/SurfaceSourceBoolJoinTelescope.v)
reuses the normalized [ContextJoin](../../proof/Phil/Core/ContextJoin.v)
and [Context](../../proof/Phil/Core/Context.v) facts. Rocq proves,
conditionally on already checked predecessor/join/insertion evidence:

- a selected Bool phi comes from one of two source operands,
  without requiring the operands to be equal;
- literal true and reflexive selected equality are justified, but
  **unproved invariants are not accepted**;
- a successful Unrestricted slot insertion requires an exactly
  fresh name, installs precisely its checked type and preserves
  all existing linear-owner lookups and the closed-loan condition;
- a successful resource join followed by this fresh slot retains
  exact linear-ownership agreement with both predecessors.

There are **no new `Axiom` or `Admitted`**. The model does **not**
prove native Haskell Map/Set/Text correctness, the actual parser,
all source error ordering or compiler-to-Rocq simulation; the
finite production witnesses exercise those independently.

## 5. Remaining FSEM-01 obligations

This first **nonempty** typed slot does not close all source
join-state semantics. Open: multiple/dependent slot telescopes,
linear or affine join-state values/transfers, general invariant
proving, failed/terminal predecessor contribution, match/decide
and loop backedges, captured resources, accepted-construct
coverage, and a general source↔production↔Rocq error/state
correspondence. The independent FSEM-05 extracted executable
semantics, FSEM-06 compiler refinement and FSEM-07 normative
graduation remain separately governed.
