# FSEM-01 — source-declared affine branch asymmetry and scoped-local cleanup

> **Status: bounded, non-normative source-to-production evidence.**
> Tracks [issue #1613](https://github.com/abiggerhammer/phil/issues/1613),
> [the resource/local typing exit matrix](formal-semantics-fsem01-exit-matrix-v1.md)
> R10/R11 and the preceding
> [J-1/J-2 source join slice](formal-semantics-source-branch-join-fsem01-v1.md).
> This is not general Phase 1 if/match elaboration, type soundness or
> universal Haskell-to-Rocq implementation refinement.

## 1. Checked nominal affine source authority

The accepted Grammar-v1 source witness is:

~~~phil
data Permit mode affine = Permit(U64);
fn choose(flag : Bool, permit : Permit, payload : Bytes[8])
    -> Bytes[8] satisfies C {
  if flag join state () {
    let spare = permit;
  } else {
    unit;
  };
  return payload;
}
~~~

The [source adapter](../../src/Phil/Surface/GrammarV1/SourceAffineIfJoinResource.hs)
requires an independently supplied, **admitted** nominal lifecycle or
resource justification for source-declared `Permit mode affine`.
It calls existing `grammarV1CheckedClosedDataMode`, then exact
`grammarV1CheckedTypeModeWithNamedResolutions` for all three function
parameters and its return, retaining the resolved GenericTypeKind,
DeclarationKey and InterfaceRevision. The source condition is checked
Unrestricted Bool; Permit is checked Affine only with external admission;
Bytes[N] is intrinsically Linear. Source spelling is not semantic
permission to strengthen nominal resource mode.

The justification is an **external trusted premise**. This fragment
does not prove the soundness of that attestation or discharge
`satisfies C`. Absent justification, unadmitted text and a declared
Unrestricted mode that weakens a Linear constructor are independently
tested against exact nominal checker errors.

## 2. Scope exit is evaluated by the production checker BEFORE the join

The adapter uses the production
[JoinStateScope](../../src/Phil/Surface/GrammarV1/JoinStateScope.hs)
to resolve source Bool condition, both predecessor bodies, fresh local
let-binders and the post-join result. It maps names to exact
declaration-rooted Core identities; matching display spelling cannot
masquerade as the same resource.

The new bounded
[Surface checker entrypoint](../../src/Phil/Surface/Check/Engine.hs)
does the following for **both statically possible predecessors**:

1. Initializes one actual production Γ/A/Δ/shared-loan context from the
   three source-checked function parameters. Both arms start from that
   same native resource context.
2. Executes the existing `checkBlock` on each source-derived arm, and
   records a complete **raw** Core context from each real successor.
3. Calls existing production `pruneScopedPath` against the exact incoming
   binder-name set. This invokes `removeScopedBinding` for disposable
   Affine/Unrestricted locals. A live Linear branch-local owner must reject
   as `LinearCompletion`. Failed pruning yields **no** post-prune context.
4. Records successful **pruned** native contexts, then calls existing
   `joinExclusive` → `Core.Context.joinContinuing`. Continuing predecessors
   need matching unrestricted/linear maps; their retained affine map is
   the intersection. Active loans prohibit an ordinary join.
5. On success, runs ordinary production `checkStatements` and
   `finalizePath` for the source-derived post-join return. The separate
   ordinary and traced entrypoints run these production steps and must
   return identical outcomes.

The source checker does **not** select just the run-time Bool branch.
The fragment remains opt-in: the established SurfaceExpression type
does not yet contain a generic if expression or full source CFG
elaborator. The source adapter admits one nonrecursive nongeneric
function, one explicit if with empty `join state ()`, a single Unit
or local let from an existing parameter in each arm, followed by an
exact Bytes[N] return (optionally preceded by a source occurrence of
Permit to test stale reuse). Unsupported source forms return
`Nothing`; that does not make them normatively invalid.

## 3. Direct source witness and precise native failures

The [strict source test driver](../../test/Phase1FSEM01AffineJoinScopeMain.hs)
parses 15 real fixtures and asserts the exact before/raw/pruned/join
native maps and errors:

| Witness | Observed native behavior required |
| --- | --- |
| [Accepted asymmetric](../../test/fixtures/fsem01-affine-join-scope-v1/accepted-asymmetric.phil) | Then moves Permit to fresh Affine `spare`; raw A has spare, pruned A is empty. Else retains Permit. Joined A must be empty, while the Linear payload and Unrestricted flag remain unchanged. Returning Bytes succeeds. |
| [Both retain Permit](../../test/fixtures/fsem01-affine-join-scope-v1/retained-affine.phil) | Raw and pruned A contain Permit in both arms; native Core join retains exactly that owner. |
| [Both create affine locals](../../test/fixtures/fsem01-affine-join-scope-v1/both-local-affine.phil) | Same display name `spare` receives two different source-rooted Core identities. Each raw arm contains its own affine local, and production scoped cleanup removes both before join. |
| [Unrestricted local](../../test/fixtures/fsem01-affine-join-scope-v1/unrestricted-local.phil) | Extra `scratch` copied from Bool exists in raw Γ only; actual production scope exit removes it. |
| [Live linear branch-local](../../test/fixtures/fsem01-affine-join-scope-v1/unreleased-linear-local.phil) | Minimal source mutation changes only `let spare = permit;` to `let spare = payload;`. Actual `pruneScopedPath` rejects **LinearCompletion**, with exact detail `linear branch-local binding remains live: <Core Name>`. No pruned successor, else-arm observation or joined state is fabricated. |
| [Stale post-join affine](../../test/fixtures/fsem01-affine-join-scope-v1/stale-after-join.phil) | Adding the single source statement `permit;` after an asymmetric join rejects **StructuralUse**; absent affine ownership is not silently resurrected. |
| Unjustified, unadmitted and mode-weakening | The existing nominal-mode gate rejects with precise missing/unadmitted/weakening causes before production branch evaluation. |
| Wrong result/condition, nonempty join telescope, unknown initializer, out-of-scope local, unsupported nested borrow | Explicit **non-competence** of this bounded adapter; these specimens are not universal source-invalidity claims. |

The driver compares the real source-derived Core contexts to independent
`Core.joinContinuing` checks. Its production rejection assertions inspect
the actual error class and detail; the existence of fixture filenames
alone is never treated as proof.

## 4. Conditional Rocq model and evidence boundary

[SurfaceSourceAffineJoinScopeBridge.v](../../proof/Phil/Surface/SurfaceSourceAffineJoinScopeBridge.v)
builds on [ContextJoin.v](../../proof/Phil/Core/ContextJoin.v). Its
`ScopedLinearPruneSafe` and `ScopedAffinePrune` are **normalized premises**,
not assertions that Rocq has proven arbitrary Haskell scope pruning.
The theorems establish, conditionally on those premises:

- a live branch-local Linear owner contradicts successful scoped pruning;
- an Affine owner absent in either continuing predecessor cannot reappear
  after a model join;
- a scoped Affine local pruned before join is not retained afterwards;
- an Affine owner present in both continuing predecessors remains
  present at the same type;
- pruning preserves unrelated Linear spectators and a successful join
  preserves their exact lookups;
- a successful model join contains no active loans.

Rocq 9.2 checks the model without new `Admitted`, `Axiom` or
`Parameter`. The finite production Haskell witnesses are separate.
This does **not** prove native Map/Set/Text implementation correctness,
universal source-to-Rocq simulation, source error-path completeness,
a sound external lifecycle attestation or full assurance discharge.

## 5. Still open after this bounded extension

This improves the J-1/J-2 evidence for FSEM-01 but does **not**
close the rule family or Phase 1: nonempty explicit join-state
telescopes, source loan regions across branches, nested or match/decide
control, general affine post-state carriers and resource carrying
terminal/failure variants remain for later slices. Also still open:
generalized loops and captures, nested aggregates, representation/error
simulation, and the separately governed FSEM-05 executable semantics,
FSEM-06 compiler correspondence and FSEM-07 normative review.

Never equate bounded adapter `Nothing` with a normative error, or a
Rocq model theorem with a general Haskell-to-Rocq refinement proof.
